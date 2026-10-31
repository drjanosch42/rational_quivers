module

public import RationalQuivers.Gelfand.Rational
public import RationalQuivers.Gelfand.Species.Rational
public import RationalQuivers.Descent.Galois
public import RationalQuivers.Species.Rep.GelfandDescent

@[expose] public section

/-!
# Weight-line modules: the shared construction behind `§6`'s three examples

Stage **S9**.  As-built addition to `PLAN.md` §S9 §2's module set (the `Quiver/Models.lean` /
`Species/Examples.lean` / `Gelfand/Models.lean` precedent), disclosed in `PLAN.md` §S9's dated
as-built banner and in `stages/S9/DESIGN-NOTES.md` §2.

Every one of `§6`'s modules — `F_ℓ` (§6.1), `D_ℓ = D_ℓ⁺ ⊕ D_ℓ⁻` (§6.2), `P_{ℓ,ε}` and
`P^∨_{ℓ,ε}` (§6.3) — is a `ℚ[√-1]`-rational Harish-Chandra module all of whose weight spaces
`M_n = M[χ_n]` are **at most one-dimensional**, supported on a set `S ⊆ ℤ` of a single parity.
They differ only in `S` and in the two scalar families by which `X` and `Y` act.  This module
builds such a module once, from `(S, x)`, and the three example modules instantiate it.

## The datum

* `S : ℤ → Prop` — the support, i.e. the set of weights `n` with `M_n ≠ 0`;
* `x : ℤ → ℚ` — the raising scalar, `X · e_n = x(n) · e_{n+2}` (read as `0` when `n + 2 ∉ S`).

The lowering scalar is **not** a second parameter: `§3.4`'s complex conjugation `c` satisfies
`c X = Y c` (the `RationalSetupOver.conj_X` field) and `c e_n = e_{-n}`, which forces `Y · e_n =
x(-n) · e_{n-2}`.  Carrying one family rather than two is what makes `conj_X`/`conj_Y` hold by
construction rather than by hypothesis.

## The hypotheses, and why they are the right ones

`wtSl2` (`[X,Y] = H`) and `wtCas` (the Casimir is the scalar `ℓ²`) are the only two conditions on
`(S, x)`; both are elementary identities in `ℚ` with a case split on `S`.  They are *independent*
inputs rather than one derived from the other exactly at the walls: at a weight `n ∈ S` with
`n + 2 ∉ S` the Casimir condition alone does not give `[X,Y] = H` unless `ℓ² = (n+1)²`, which is
the source's own statement that the `𝔰𝔩₂`-string of `M` may only stop where the paper says it
stops (`§6.1`'s `M_{ℓ-1}` lowest weight space, `§6.2`'s `D_ℓ^{±}[χ_{±(ℓ+1)}]`).

`wtSymm` (`S` is stable under `n ↦ -n`) and `wtPar` (every weight has the parity of `ℓ - 1`, i.e.
`RQ-3.03-C3`'s central character) complete the datum.

## The `ℚ`-form

`RationalSetupOver.baseChange` is **not** built by exhibiting a `ℚ`-basis: the conjugation `c` swaps
`M_n` and `M_{-n}`, so the weight basis is not defined over `ℚ` and an explicit `ℚ`-basis would be
a change-of-basis computation with nothing to say.  Instead S0's Galois descent
(`Descent.descentCounit_bijective`, census `RQ-1.13`) is applied to the `VecK ℚ ℚ[√-1]` object
carried by `c` itself: the `ℚ`-form **is** `M^{Gal(ℚ[√-1]/ℚ)}`, and `baseChange` is the counit,
which `RQ-1.13` says is an isomorphism.  This is `thm:galoisdescent` used for exactly what it is
for, and it makes `conj_baseChange` (`c` fixes `1 ⊗ v`) true by the definition of the fixed points.

@census none (helper module: no census row is claimed here; the three example modules claim
`RQ2-6.01`–`RQ2-6.03`)
-/

universe u

namespace RationalQuivers.Examples

open RationalQuivers.HC RationalQuivers.Gelfand RationalQuivers.Descent CategoryTheory
open RationalQuivers.Gelfand.RationalStructure (gelfandQ vtxQ edgeQ RepNilQ)
open RationalQuivers.Gelfand.Cyclic (cyclicQ vtxC edgeC RepNilCycQ)
open scoped TensorProduct

/-- `ℚ[√-1]` as a module over the engine's `SqrtNegOneExt.qi.carrier` (the same field; instance
search does not unfold the projection).  @census none (helper) -/
noncomputable local instance instModuleQiCarrier (M : Type) [AddCommGroup M] [Module (Qi : Type) M] :
    Module SqrtNegOneExt.qi.carrier M := ‹Module (Qi : Type) M›

/-! ## The carrier and its weight lines -/

/-- The index set of the weight basis: the weights in the support `S`.  @census none (helper) -/
abbrev WtIdx (S : ℤ → Prop) : Type := {n : ℤ // S n}

/-- The carrier `M = ⨁_{n ∈ S} ℚ[√-1]·e_n`.  @census none (helper) -/
abbrev WtCar (S : ℤ → Prop) : Type := WtIdx S →₀ (Qi : Type)

variable {S : ℤ → Prop} [DecidablePred S] {x : ℤ → ℚ}

/-- The basis vector `e_n`, `n ∈ S`.  @census none (helper) -/
noncomputable def wtE (i : WtIdx S) : WtCar S := Finsupp.single i 1

/-- `M_n`: the line `ℚ[√-1]·e_n` for `n ∈ S`, and `0` otherwise.  @census none (helper) -/
noncomputable def wtComp (S : ℤ → Prop) [DecidablePred S] (n : ℤ) :
    Submodule (Qi : Type) (WtCar S) :=
  if h : S n then LinearMap.range (Finsupp.lsingle (M := (Qi : Type)) (⟨n, h⟩ : WtIdx S)) else ⊥

theorem wtComp_of_mem {n : ℤ} (h : S n) :
    wtComp S n = LinearMap.range (Finsupp.lsingle (M := (Qi : Type)) (⟨n, h⟩ : WtIdx S)) := by
  rw [wtComp, dif_pos h]

theorem wtComp_of_not_mem {n : ℤ} (h : ¬ S n) : wtComp S n = ⊥ := by rw [wtComp, dif_neg h]

theorem single_mem_wtComp (i : WtIdx S) (a : (Qi : Type)) :
    Finsupp.single i a ∈ wtComp S (i : ℤ) := by
  rw [wtComp_of_mem i.2]
  exact ⟨a, by cases i; rfl⟩

theorem eq_zero_of_mem_wtComp_not_mem {n : ℤ} (h : ¬ S n) {v : WtCar S} (hv : v ∈ wtComp S n) :
    v = 0 := by
  rw [wtComp_of_not_mem h, Submodule.mem_bot] at hv; exact hv

/-- Every element of `M_n`, `n ∈ S`, is a multiple of `e_n`.  @census none (helper) -/
theorem exists_single_of_mem_wtComp {n : ℤ} (h : S n) {v : WtCar S} (hv : v ∈ wtComp S n) :
    ∃ a : (Qi : Type), v = Finsupp.single (⟨n, h⟩ : WtIdx S) a := by
  rw [wtComp_of_mem h] at hv
  obtain ⟨a, ha⟩ := hv
  exact ⟨a, ha.symm⟩

/-- `M = ⨁_n M_n`.  @census none (helper) -/
theorem wtComp_isInternal : DirectSum.IsInternal (wtComp S) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · intro n
    by_cases hn : S n
    · have hle : (⨆ (m : ℤ) (_ : m ≠ n), wtComp S m)
          ≤ ⨆ (j : WtIdx S) (_ : j ≠ (⟨n, hn⟩ : WtIdx S)),
              LinearMap.range (Finsupp.lsingle (M := (Qi : Type)) j) := by
        refine iSup_le fun m => iSup_le fun hm => ?_
        by_cases hms : S m
        · rw [wtComp_of_mem hms]
          refine le_iSup_of_le (⟨m, hms⟩ : WtIdx S) (le_iSup_of_le ?_ le_rfl)
          intro hcon
          exact hm (congrArg Subtype.val hcon)
        · rw [wtComp_of_not_mem hms]; exact bot_le
      refine Disjoint.mono_right hle ?_
      rw [wtComp_of_mem hn]
      exact iSupIndep_range_lsingle (WtIdx S) (Qi : Type) (Qi : Type) ⟨n, hn⟩
    · rw [wtComp_of_not_mem hn]; exact disjoint_bot_left
  · refine le_antisymm le_top ?_
    rw [← Finsupp.iSup_lsingle_range (R := (Qi : Type)) (M := (Qi : Type)) (α := WtIdx S)]
    exact iSup_le fun i => le_iSup_of_le (i : ℤ) (by rw [wtComp_of_mem i.2])

/-! ## The three operators -/

/-- `H · e_n = n · e_n`.  @census none (helper) -/
noncomputable def wtH (S : ℤ → Prop) [DecidablePred S] : Module.End (Qi : Type) (WtCar S) :=
  Finsupp.lsum ℕ fun i : WtIdx S => (((i : ℤ) : (Qi : Type))) • Finsupp.lsingle i

/-- `X · e_n = x(n) · e_{n+2}`, read as `0` when `n + 2 ∉ S`.  @census none (helper) -/
noncomputable def wtX (S : ℤ → Prop) [DecidablePred S] (x : ℤ → ℚ) :
    Module.End (Qi : Type) (WtCar S) :=
  Finsupp.lsum ℕ fun i : WtIdx S =>
    if h : S ((i : ℤ) + 2) then
      ((x (i : ℤ) : (Qi : Type))) • Finsupp.lsingle (⟨(i : ℤ) + 2, h⟩ : WtIdx S) else 0

/-- `Y · e_n = x(-n) · e_{n-2}`, read as `0` when `n - 2 ∉ S`.  The scalar is `x(-n)`, not a
second parameter: see the module docstring.  @census none (helper) -/
noncomputable def wtY (S : ℤ → Prop) [DecidablePred S] (x : ℤ → ℚ) :
    Module.End (Qi : Type) (WtCar S) :=
  Finsupp.lsum ℕ fun i : WtIdx S =>
    if h : S ((i : ℤ) - 2) then
      ((x (-(i : ℤ)) : (Qi : Type))) • Finsupp.lsingle (⟨(i : ℤ) - 2, h⟩ : WtIdx S) else 0

@[simp] theorem wtH_single (i : WtIdx S) (a : (Qi : Type)) :
    wtH S (Finsupp.single i a) = Finsupp.single i (((i : ℤ) : (Qi : Type)) * a) := by
  rw [wtH, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply, Finsupp.smul_single,
    smul_eq_mul]

theorem wtX_single (i : WtIdx S) (a : (Qi : Type)) :
    wtX S x (Finsupp.single i a)
      = if h : S ((i : ℤ) + 2) then
          Finsupp.single (⟨(i : ℤ) + 2, h⟩ : WtIdx S) ((x (i : ℤ) : (Qi : Type)) * a) else 0 := by
  rw [wtX, Finsupp.lsum_single]
  by_cases h : S ((i : ℤ) + 2)
  · rw [dif_pos h, dif_pos h, LinearMap.smul_apply, Finsupp.lsingle_apply, Finsupp.smul_single,
      smul_eq_mul]
  · rw [dif_neg h, dif_neg h, LinearMap.zero_apply]

theorem wtY_single (i : WtIdx S) (a : (Qi : Type)) :
    wtY S x (Finsupp.single i a)
      = if h : S ((i : ℤ) - 2) then
          Finsupp.single (⟨(i : ℤ) - 2, h⟩ : WtIdx S) ((x (-(i : ℤ)) : (Qi : Type)) * a)
        else 0 := by
  rw [wtY, Finsupp.lsum_single]
  by_cases h : S ((i : ℤ) - 2)
  · rw [dif_pos h, dif_pos h, LinearMap.smul_apply, Finsupp.lsingle_apply, Finsupp.smul_single,
      smul_eq_mul]
  · rw [dif_neg h, dif_neg h, LinearMap.zero_apply]

/-- `X · e_n` when `n + 2` is in the support, with the target index normalized.
@census none (helper) -/
theorem wtX_single_eq {i j : WtIdx S} (hj : (j : ℤ) = (i : ℤ) + 2) (a : (Qi : Type)) :
    wtX S x (Finsupp.single i a) = Finsupp.single j ((x (i : ℤ) : (Qi : Type)) * a) := by
  have hS : S ((i : ℤ) + 2) := hj ▸ j.2
  rw [wtX_single, dif_pos hS]
  congr 1
  exact Subtype.ext hj.symm

/-- `X · e_n = 0` when `n + 2` is outside the support.  @census none (helper) -/
theorem wtX_single_eq_zero {i : WtIdx S} (h : ¬ S ((i : ℤ) + 2)) (a : (Qi : Type)) :
    wtX S x (Finsupp.single i a) = 0 := by rw [wtX_single, dif_neg h]

/-- `Y · e_n` when `n - 2` is in the support, with the target index normalized.
@census none (helper) -/
theorem wtY_single_eq {i j : WtIdx S} (hj : (j : ℤ) = (i : ℤ) - 2) (a : (Qi : Type)) :
    wtY S x (Finsupp.single i a) = Finsupp.single j ((x (-(i : ℤ)) : (Qi : Type)) * a) := by
  have hS : S ((i : ℤ) - 2) := hj ▸ j.2
  rw [wtY_single, dif_pos hS]
  congr 1
  exact Subtype.ext hj.symm

/-- `Y · e_n = 0` when `n - 2` is outside the support.  @census none (helper) -/
theorem wtY_single_eq_zero {i : WtIdx S} (h : ¬ S ((i : ℤ) - 2)) (a : (Qi : Type)) :
    wtY S x (Finsupp.single i a) = 0 := by rw [wtY_single, dif_neg h]

/-! ## The two conditions on `(S, x)` -/

/-- `[X,Y] = H`, read on the weight line `M_n`: `x(n-2)·x(-n) − x(-(n+2))·x(n) = n`, with each
product deleted when the intermediate weight leaves the support.  @census none (helper) -/
def WtSl2 (S : ℤ → Prop) [DecidablePred S] (x : ℤ → ℚ) : Prop :=
  ∀ n : ℤ, S n →
    (if S (n - 2) then x (n - 2) * x (-n) else 0)
      - (if S (n + 2) then x (-(n + 2)) * x n else 0) = (n : ℚ)

/-- The Casimir `C = H² − 2H + 4XY + 1` acts on `M_n` by the scalar `ℓ²` — the generalized
infinitesimal character of `RQ-3.02` in its sharpest form (`m = 1`, not merely nilpotent).
@census none (helper) -/
def WtCas (ℓ : ℕ) (S : ℤ → Prop) [DecidablePred S] (x : ℤ → ℚ) : Prop :=
  ∀ n : ℤ, S n →
    (n : ℚ) ^ 2 - 2 * (n : ℚ) + 4 * (if S (n - 2) then x (n - 2) * x (-n) else 0) + 1
      = (ℓ : ℚ) ^ 2

/-- The support is stable under `n ↦ -n` — what `c(M_n) = M_{-n}` needs.  @census none (helper) -/
def WtSymm (S : ℤ → Prop) : Prop := ∀ n : ℤ, S n → S (-n)

/-- Every weight has the parity of `ℓ - 1`: the central character `RQ-3.03-C3`.
@census none (helper) -/
def WtPar (ℓ : ℕ) (S : ℤ → Prop) : Prop := ∀ n : ℤ, S n → (n - ((ℓ : ℤ) - 1)) % 2 = 0

/-! ## The graded `𝔰𝔩₂`-module -/

theorem wtLie_H_X : wtH S * wtX S x - wtX S x * wtH S = (2 : (Qi : Type)) • wtX S x := by
  refine Finsupp.lhom_ext fun i a => ?_
  by_cases h : S ((i : ℤ) + 2)
  · have hj : ((⟨(i : ℤ) + 2, h⟩ : WtIdx S) : ℤ) = ((i : ℤ)) + 2 := rfl
    show wtH S (wtX S x (Finsupp.single i a)) - wtX S x (wtH S (Finsupp.single i a))
      = (2 : (Qi : Type)) • wtX S x (Finsupp.single i a)
    rw [wtX_single_eq hj, wtH_single, wtH_single, wtX_single_eq hj, hj, Finsupp.smul_single,
      ← Finsupp.single_sub]
    congr 1
    push_cast
    ring
  · show wtH S (wtX S x (Finsupp.single i a)) - wtX S x (wtH S (Finsupp.single i a))
      = (2 : (Qi : Type)) • wtX S x (Finsupp.single i a)
    rw [wtX_single_eq_zero h, wtH_single, wtX_single_eq_zero h]
    simp

theorem wtLie_H_Y : wtH S * wtY S x - wtY S x * wtH S = -((2 : (Qi : Type)) • wtY S x) := by
  refine Finsupp.lhom_ext fun i a => ?_
  by_cases h : S ((i : ℤ) - 2)
  · have hj : ((⟨(i : ℤ) - 2, h⟩ : WtIdx S) : ℤ) = ((i : ℤ)) - 2 := rfl
    show wtH S (wtY S x (Finsupp.single i a)) - wtY S x (wtH S (Finsupp.single i a))
      = -((2 : (Qi : Type)) • wtY S x (Finsupp.single i a))
    rw [wtY_single_eq hj, wtH_single, wtH_single, wtY_single_eq hj, hj, Finsupp.smul_single,
      ← Finsupp.single_neg, ← Finsupp.single_sub]
    congr 1
    push_cast
    ring
  · show wtH S (wtY S x (Finsupp.single i a)) - wtY S x (wtH S (Finsupp.single i a))
      = -((2 : (Qi : Type)) • wtY S x (Finsupp.single i a))
    rw [wtY_single_eq_zero h, wtH_single, wtY_single_eq_zero h]
    simp

theorem wtLie_X_Y (hrel : WtSl2 S x) : wtX S x * wtY S x - wtY S x * wtX S x = wtH S := by
  refine Finsupp.lhom_ext fun i a => ?_
  have hn := hrel (i : ℤ) i.2
  show wtX S x (wtY S x (Finsupp.single i a)) - wtY S x (wtX S x (Finsupp.single i a))
    = wtH S (Finsupp.single i a)
  have hXY : wtX S x (wtY S x (Finsupp.single i a))
      = Finsupp.single i
        (((if S ((i : ℤ) - 2) then x ((i : ℤ) - 2) * x (-(i : ℤ)) else 0 : ℚ)
          : (Qi : Type)) * a) := by
    by_cases h : S ((i : ℤ) - 2)
    · have hj : ((⟨(i : ℤ) - 2, h⟩ : WtIdx S) : ℤ) = ((i : ℤ)) - 2 := rfl
      have hi : ((i : ℤ)) = ((⟨(i : ℤ) - 2, h⟩ : WtIdx S) : ℤ) + 2 := by rw [hj]; ring
      rw [wtY_single_eq hj, wtX_single_eq hi, hj, if_pos h]
      push_cast
      ring_nf
    · rw [wtY_single_eq_zero h, if_neg h, map_zero]
      simp
  have hYX : wtY S x (wtX S x (Finsupp.single i a))
      = Finsupp.single i
        (((if S ((i : ℤ) + 2) then x (-((i : ℤ) + 2)) * x (i : ℤ) else 0 : ℚ)
          : (Qi : Type)) * a) := by
    by_cases h : S ((i : ℤ) + 2)
    · have hj : ((⟨(i : ℤ) + 2, h⟩ : WtIdx S) : ℤ) = ((i : ℤ)) + 2 := rfl
      have hi : ((i : ℤ)) = ((⟨(i : ℤ) + 2, h⟩ : WtIdx S) : ℤ) - 2 := by rw [hj]; ring
      rw [wtX_single_eq hj, wtY_single_eq hi, hj, if_pos h]
      push_cast
      ring_nf
    · rw [wtX_single_eq_zero h, if_neg h, map_zero]
      simp
  rw [hXY, hYX, wtH_single, ← Finsupp.single_sub, ← sub_mul]
  congr 2
  rw [← Rat.cast_sub, hn]
  push_cast
  ring

/-- **The graded `𝔰𝔩₂`-module** `M = ⨁_{n ∈ S} ℚ[√-1]·e_n` with `H·e_n = n·e_n`,
`X·e_n = x(n)·e_{n+2}`, `Y·e_n = x(-n)·e_{n-2}`.  @census none (helper) -/
noncomputable def wtWeight (S : ℤ → Prop) [DecidablePred S] (x : ℤ → ℚ) (hrel : WtSl2 S x) :
    WeightData (Qi : Type) (WtCar S) where
  comp := wtComp S
  isInternal := wtComp_isInternal
  H := wtH S
  X := wtX S x
  Y := wtY S x
  H_apply n v hv := by
    by_cases hn : S n
    · obtain ⟨a, rfl⟩ := exists_single_of_mem_wtComp (S := S) hn hv
      rw [wtH_single, Finsupp.smul_single]
      rfl
    · rw [eq_zero_of_mem_wtComp_not_mem (S := S) hn hv]; simp
  X_mem n v hv := by
    by_cases hn : S n
    · obtain ⟨a, rfl⟩ := exists_single_of_mem_wtComp (S := S) hn hv
      by_cases h : S (n + 2)
      · have hj : ((⟨n + 2, h⟩ : WtIdx S) : ℤ) = ((⟨n, hn⟩ : WtIdx S) : ℤ) + 2 := rfl
        rw [wtX_single_eq hj]
        exact single_mem_wtComp (⟨n + 2, h⟩ : WtIdx S) _
      · rw [wtX_single_eq_zero h]; exact Submodule.zero_mem _
    · rw [eq_zero_of_mem_wtComp_not_mem (S := S) hn hv, map_zero]; exact Submodule.zero_mem _
  Y_mem n v hv := by
    by_cases hn : S n
    · obtain ⟨a, rfl⟩ := exists_single_of_mem_wtComp (S := S) hn hv
      by_cases h : S (n - 2)
      · have hj : ((⟨n - 2, h⟩ : WtIdx S) : ℤ) = ((⟨n, hn⟩ : WtIdx S) : ℤ) - 2 := rfl
        rw [wtY_single_eq hj]
        exact single_mem_wtComp (⟨n - 2, h⟩ : WtIdx S) _
      · rw [wtY_single_eq_zero h]; exact Submodule.zero_mem _
    · rw [eq_zero_of_mem_wtComp_not_mem (S := S) hn hv, map_zero]; exact Submodule.zero_mem _
  lie_H_X := wtLie_H_X
  lie_H_Y := wtLie_H_Y
  lie_X_Y := wtLie_X_Y hrel

/-! ## The Casimir is the scalar `ℓ²` -/

@[simp] theorem wtWeight_comp (hrel : WtSl2 S x) : (wtWeight S x hrel).comp = wtComp S := rfl
@[simp] theorem wtWeight_H (hrel : WtSl2 S x) : (wtWeight S x hrel).H = wtH S := rfl
@[simp] theorem wtWeight_X (hrel : WtSl2 S x) : (wtWeight S x hrel).X = wtX S x := rfl
@[simp] theorem wtWeight_Y (hrel : WtSl2 S x) : (wtWeight S x hrel).Y = wtY S x := rfl

theorem wtXY_single (i : WtIdx S) (a : (Qi : Type)) :
    wtX S x (wtY S x (Finsupp.single i a))
      = Finsupp.single i
        (((if S ((i : ℤ) - 2) then x ((i : ℤ) - 2) * x (-(i : ℤ)) else 0 : ℚ)
          : (Qi : Type)) * a) := by
  by_cases h : S ((i : ℤ) - 2)
  · have hj : ((⟨(i : ℤ) - 2, h⟩ : WtIdx S) : ℤ) = ((i : ℤ)) - 2 := rfl
    have hi : ((i : ℤ)) = ((⟨(i : ℤ) - 2, h⟩ : WtIdx S) : ℤ) + 2 := by rw [hj]; ring
    rw [wtY_single_eq hj, wtX_single_eq hi, hj, if_pos h]
    push_cast
    ring_nf
  · rw [wtY_single_eq_zero h, if_neg h, map_zero]
    simp

/-- The Casimir acts on the whole module by the scalar `ℓ²` — not merely nilpotently.
@census none (helper) -/
theorem wtCasimir_eq (ℓ : ℕ) (hrel : WtSl2 S x) (hcas : WtCas ℓ S x) :
    (wtWeight S x hrel).casimir
      = (algebraMap ℚ (Qi : Type) ((ℓ : ℚ) ^ 2)) • (1 : Module.End (Qi : Type) (WtCar S)) := by
  refine Finsupp.lhom_ext fun i a => ?_
  set c : ℚ := (if S ((i : ℤ) - 2) then x ((i : ℤ) - 2) * x (-(i : ℤ)) else 0) with hcdef
  have hn : ((i : ℤ) : ℚ) ^ 2 - 2 * ((i : ℤ) : ℚ) + 4 * c + 1 = (ℓ : ℚ) ^ 2 := hcas (i : ℤ) i.2
  rw [(wtWeight S x hrel).casimir_apply]
  simp only [wtWeight_H, wtWeight_X, wtWeight_Y, LinearMap.smul_apply, Module.End.one_apply]
  rw [wtH_single, wtH_single, wtXY_single, ← hcdef, Finsupp.smul_single, Finsupp.smul_single,
    Finsupp.smul_single, ← Finsupp.single_sub, ← Finsupp.single_add, ← Finsupp.single_add]
  congr 1
  have hq := congrArg (fun r : ℚ => (r : (Qi : Type))) hn
  push_cast at hq
  have halg : (algebraMap ℚ (Qi : Type)) ((ℓ : ℚ) ^ 2) = ((ℓ : (Qi : Type)) ^ 2) := by
    rw [map_pow, map_natCast]
  rw [halg]
  simp only [smul_eq_mul]
  linear_combination a * hq

/-- The scalar by which `C` acts on the weight line `M_n`:
`κ(n) = n² − 2n + 4·x(n−2)·x(−n) + 1`.  @census none (helper) -/
noncomputable def wtKappa (S : ℤ → Prop) [DecidablePred S] (x : ℤ → ℚ) (n : ℤ) : ℚ :=
  (n : ℚ) ^ 2 - 2 * (n : ℚ) + 4 * (if S (n - 2) then x (n - 2) * x (-n) else 0) + 1

/-- **`C` is diagonal on the weight basis**: `C · e_n = κ(n) · e_n`.  This is `wtCasimir_eq`'s own
computation with the `WtCas` hypothesis removed, and it is what makes `wtCas_of_gic` possible.
@census none (helper) -/
theorem wtCasimir_single (hrel : WtSl2 S x) (i : WtIdx S) (a : (Qi : Type)) :
    (wtWeight S x hrel).casimir (Finsupp.single i a)
      = Finsupp.single i (((wtKappa S x (i : ℤ) : ℚ) : (Qi : Type)) * a) := by
  rw [(wtWeight S x hrel).casimir_apply]
  simp only [wtWeight_H, wtWeight_X, wtWeight_Y, LinearMap.smul_apply, Module.End.one_apply]
  rw [wtH_single, wtH_single, wtXY_single]
  simp only [Finsupp.smul_single, smul_eq_mul]
  rw [← Finsupp.single_sub, ← Finsupp.single_add, ← Finsupp.single_add]
  congr 1
  simp only [wtKappa]
  push_cast
  ring

/-- `(C − λ)^m` on a basis vector.  @census none (helper) -/
theorem wtCasimirSub_pow_single (ℓ : ℕ) (hrel : WtSl2 S x) (i : WtIdx S) :
    ∀ (m : ℕ) (a : (Qi : Type)),
      (((wtWeight S x hrel).casimir
          - (algebraMap ℚ (Qi : Type) ((ℓ : ℚ) ^ 2))
            • (1 : Module.End (Qi : Type) (WtCar S))) ^ m) (Finsupp.single i a)
        = Finsupp.single i ((((wtKappa S x (i : ℤ) - (ℓ : ℚ) ^ 2 : ℚ)) : (Qi : Type)) ^ m * a) := by
  have hstep : ∀ b : (Qi : Type),
      ((wtWeight S x hrel).casimir
        - (algebraMap ℚ (Qi : Type) ((ℓ : ℚ) ^ 2))
          • (1 : Module.End (Qi : Type) (WtCar S))) (Finsupp.single i b)
      = Finsupp.single i ((((wtKappa S x (i : ℤ) - (ℓ : ℚ) ^ 2 : ℚ)) : (Qi : Type)) * b) := by
    intro b
    rw [LinearMap.sub_apply, wtCasimir_single, LinearMap.smul_apply, Module.End.one_apply,
      Finsupp.smul_single, ← Finsupp.single_sub]
    congr 1
    have halg : (algebraMap ℚ (Qi : Type)) ((ℓ : ℚ) ^ 2) = ((ℓ : (Qi : Type)) ^ 2) := by
      rw [map_pow, map_natCast]
    rw [halg, smul_eq_mul]
    push_cast
    ring
  intro m
  induction m with
  | zero => intro a; simp
  | succ m ih =>
      intro a
      rw [pow_succ', Module.End.mul_apply, ih, hstep]
      congr 1
      rw [pow_succ']
      ring

/-- **On a weight line a *generalized* infinitesimal character IS a character.**  `C` is diagonal
(`wtCasimir_single`), so `(C − ℓ²)^m = 0` forces `κ(n) = ℓ²` at every weight in the support — which
is exactly `WtCas`.  Together with `wtGIC` this makes `WtCas ℓ S x` and
`HasGeneralizedInfinitesimalCharacter (wtWeight S x hrel) ℓ` **equivalent**, so design decision
`D-S9-3` sharpens nothing on this class of objects: it states the condition membership of
`HC_{ℓ²}(𝔤,K)` already requires.  See `DESIGN-NOTES.md` §14.  @census none (helper) -/
theorem wtCas_of_gic (ℓ : ℕ) (hrel : WtSl2 S x)
    (hgic : HasGeneralizedInfinitesimalCharacter (wtWeight S x hrel) ℓ) : WtCas ℓ S x := by
  obtain ⟨m, hm⟩ := hgic
  intro n hn
  have h := congrArg (fun f : Module.End (Qi : Type) (WtCar S) =>
    f (Finsupp.single (⟨n, hn⟩ : WtIdx S) (1 : (Qi : Type)))) hm
  simp only [LinearMap.zero_apply] at h
  rw [wtCasimirSub_pow_single] at h
  have hz : (((wtKappa S x n - (ℓ : ℚ) ^ 2 : ℚ)) : (Qi : Type)) ^ m * 1 = 0 :=
    Finsupp.single_eq_zero.mp h
  rw [mul_one] at hz
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · exact absurd hz (by simp)
  · have h0 : (((wtKappa S x n - (ℓ : ℚ) ^ 2 : ℚ)) : (Qi : Type)) = 0 :=
      (pow_eq_zero_iff hmpos.ne').mp hz
    have hq : (wtKappa S x n - (ℓ : ℚ) ^ 2 : ℚ) = 0 := by exact_mod_cast h0
    simp only [wtKappa] at hq
    linarith [hq]

/-- The generalized infinitesimal character `λ = ℓ²` (`RQ-3.02`), at nilpotency degree `1`.
@census none (helper) -/
theorem wtGIC (ℓ : ℕ) (hrel : WtSl2 S x) (hcas : WtCas ℓ S x) :
    HasGeneralizedInfinitesimalCharacter (wtWeight S x hrel) ℓ := by
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact sub_eq_zero_of_eq (wtCasimir_eq ℓ hrel hcas)

/-- **`D-S9-3` sharpens nothing.**  On a weight line the two conditions are *equivalent*: `WtCas`
(the Casimir **is** the scalar `ℓ²`) and `RQ-3.02`'s generalized infinitesimal character (`C − ℓ²`
nilpotent) say the same thing, because `C` is diagonal on the weight basis (`wtCasimir_single`) and
a diagonal nilpotent is zero.

This is the answer to "is `RQ2-6.01-C7` / `RQ2-6.02-C6` / `RQ2-6.03-C5` discharged by §6's
mathematics or by our encoding?".  Every term of `HC ℓ ℚ ImagUnit.qi` carries `gic` as a **field**,
so on any object of this shape the Casimir is already the scalar before `D-S9-3` says anything;
the design decision fixes the *form the hypothesis is written in*, not the class of objects it
admits.  `DESIGN-NOTES.md` §14 sets out what that does and does not settle.
@census none (helper) -/
theorem wtCas_iff_gic (ℓ : ℕ) (hrel : WtSl2 S x) :
    WtCas ℓ S x ↔ HasGeneralizedInfinitesimalCharacter (wtWeight S x hrel) ℓ :=
  ⟨fun hcas => wtGIC ℓ hrel hcas, fun hgic => wtCas_of_gic ℓ hrel hgic⟩

/-! ## The conjugation `c`

The engine (`Gelfand.RationalStructure`, `Gelfand.Equivalence`) is stated over the bundle's
involution `SqrtNegOneExt.qi.conj`; this file's construction is over `HC.galConj`.  The two are
equal (`qi_conj`), and the four standard facts about `c` are re-proved here for `galConj`. -/

/-- `c ≠ 1` in `Gal(ℚ[√-1]/ℚ)`: it moves `√-1`.  @census none (helper) -/
theorem galConj_ne_one : galConj ≠ 1 := by
  intro h
  have hI : Complex.I ∈ (Qi : IntermediateField ℚ ℂ) := IntermediateField.subset_adjoin ℚ _ rfl
  have h1 := congrArg (fun σ : (Qi : Type) ≃ₐ[ℚ] (Qi : Type) => ((σ ⟨Complex.I, hI⟩ : Qi) : ℂ)) h
  change (starRingEnd ℂ) Complex.I = Complex.I at h1
  rw [Complex.conj_I] at h1
  have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination -h1
  simp [Complex.I_ne_zero] at h2

/-- In the order-two Galois group, every element other than `1` is `c`.  @census none (helper) -/
theorem eq_galConj_of_ne_one (hcard : Nat.card ((Qi : Type) ≃ₐ[ℚ] (Qi : Type)) = 2)
    {σ : (Qi : Type) ≃ₐ[ℚ] (Qi : Type)} (hσ : σ ≠ 1) : σ = galConj := by
  obtain ⟨w, -, hu⟩ := (Nat.card_eq_two_iff' (1 : (Qi : Type) ≃ₐ[ℚ] (Qi : Type))).mp hcard
  rw [hu σ hσ, ← hu galConj galConj_ne_one]

/-- The bundle's involution is `HC.galConj`.  @census none (helper) -/
theorem qi_conj : SqrtNegOneExt.qi.conj = galConj :=
  (SqrtNegOneExt.eq_conj_of_ne_one SqrtNegOneExt.qi galConj_ne_one).symm

theorem galConj_galConj (a : (Qi : Type)) : galConj (galConj a) = a := by
  rw [← qi_conj]; exact SqrtNegOneExt.conj_conj SqrtNegOneExt.qi a

theorem galConj_mul_self : galConj * galConj = 1 := by
  exact AlgEquiv.ext fun a => galConj_galConj a

/-- `n ↦ -n` on the support.  @census none (helper) -/
def wtNeg (hsym : WtSymm S) : WtIdx S ≃ WtIdx S where
  toFun i := ⟨-(i : ℤ), hsym _ i.2⟩
  invFun i := ⟨-(i : ℤ), hsym _ i.2⟩
  left_inv i := Subtype.ext (neg_neg _)
  right_inv i := Subtype.ext (neg_neg _)

@[simp] theorem wtNeg_val (hsym : WtSymm S) (i : WtIdx S) :
    ((wtNeg hsym i : WtIdx S) : ℤ) = -(i : ℤ) := rfl

/-- **The complex conjugation** `c · (a·e_n) = c(a)·e_{-n}` (`§3.4`, the `RationalSetupOver.conj` field).
@census none (helper) -/
noncomputable def wtConj (hsym : WtSymm S) : WtCar S ≃+ WtCar S :=
  (Finsupp.mapRange.addEquiv (galConj.toRingEquiv.toAddEquiv)).trans
    (Finsupp.domCongr (wtNeg hsym))

@[simp] theorem wtConj_single (hsym : WtSymm S) (i : WtIdx S) (a : (Qi : Type)) :
    wtConj hsym (Finsupp.single i a) = Finsupp.single (wtNeg hsym i) (galConj a) := by
  show Finsupp.equivMapDomain (wtNeg hsym)
      (Finsupp.mapRange (galConj.toRingEquiv.toAddEquiv) (map_zero _) (Finsupp.single i a)) = _
  rw [Finsupp.mapRange_single, Finsupp.equivMapDomain_single]
  rfl

theorem wtConj_smul (hsym : WtSymm S) (a : (Qi : Type)) (v : WtCar S) :
    wtConj hsym (a • v) = galConj a • wtConj hsym v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [smul_add, map_add, hf, hg]
  | single i b => simp [Finsupp.smul_single, map_mul]

theorem wtConj_involutive (hsym : WtSymm S) : Function.Involutive (wtConj hsym) := by
  intro v
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i b =>
      rw [wtConj_single, wtConj_single]
      congr 1
      · exact (wtNeg hsym).left_inv i
      · exact galConj_galConj b

/-! ## The `ℚ`-form, by Galois descent (`RQ-1.13`) -/

open scoped Classical in
/-- The `Gal(ℚ[√-1]/ℚ)`-action carried by `c`: the identity at `1`, `c` at the other element.
@census none (helper) -/
@[implicit_reducible] noncomputable def wtGalAction (hsym : WtSymm S) :
    DistribMulAction ((Qi : Type) ≃ₐ[ℚ] (Qi : Type)) (WtCar S) where
  smul σ v := if σ = 1 then v else wtConj hsym v
  one_smul v := by show (if (1 : (Qi : Type) ≃ₐ[ℚ] (Qi : Type)) = 1 then v else _) = v; simp
  mul_smul σ τ v := by
    show (if σ * τ = 1 then v else wtConj hsym v)
      = (if σ = 1 then (if τ = 1 then v else wtConj hsym v)
          else wtConj hsym (if τ = 1 then v else wtConj hsym v))
    by_cases hσ : σ = 1
    · subst hσ; simp
    · by_cases hτ : τ = 1
      · subst hτ; simp [hσ]
      · have hστ : σ * τ = 1 := by
          rw [eq_galConj_of_ne_one Qi.card_gal hσ, eq_galConj_of_ne_one Qi.card_gal hτ,
            galConj_mul_self]
        rw [if_pos hστ, if_neg hσ, if_neg hτ, wtConj_involutive hsym v]
  smul_zero σ := by
    show (if σ = 1 then (0 : WtCar S) else wtConj hsym 0) = 0
    by_cases hσ : σ = 1 <;> simp [hσ]
  smul_add σ v w := by
    show (if σ = 1 then v + w else wtConj hsym (v + w))
      = (if σ = 1 then v else wtConj hsym v) + (if σ = 1 then w else wtConj hsym w)
    by_cases hσ : σ = 1 <;> simp [hσ]

open scoped Classical in
/-- The action is semi-linear: `σ • (a·v) = σ(a)·(σ • v)` (`RQ-1.16-C2`).
@census none (helper) -/
theorem wtIsSemilinear (hsym : WtSymm S) :
    letI := wtGalAction hsym
    Descent.IsSemilinearAction ℚ (Qi : Type) (WtCar S) := by
  letI := wtGalAction hsym
  refine ⟨fun σ a v => ?_⟩
  show (if σ = 1 then a • v else wtConj hsym (a • v))
    = σ a • (if σ = 1 then v else wtConj hsym v)
  by_cases hσ : σ = 1
  · subst hσ; simp
  · rw [if_neg hσ, if_neg hσ, wtConj_smul, eq_galConj_of_ne_one Qi.card_gal hσ]

open scoped Classical in
/-- The `ℚ[√-1]`-vector space `M` with the `ℚ`-structure carried by `c` — S0's `VecK ℚ ℚ[√-1]`.
@census none (helper) -/
noncomputable def wtVecK (hsym : WtSymm S) : Descent.VecK ℚ (Qi : Type) :=
  letI := wtGalAction hsym
  letI := wtIsSemilinear hsym
  { carrier := WtCar S }

open scoped Classical in
theorem wtVecK_carrier (hsym : WtSymm S) : (wtVecK hsym).carrier = WtCar S := rfl

open scoped Classical in
/-- **The `ℚ`-form** `M_ℚ = M^{Gal(ℚ[√-1]/ℚ)}`.  @census none (helper) -/
noncomputable def wtFormSubmodule (hsym : WtSymm S) : Submodule ℚ (WtCar S) :=
  Descent.fixedPoints ℚ (Qi : Type) (wtVecK hsym)

open scoped Classical in
theorem mem_wtFormSubmodule (hsym : WtSymm S) {v : WtCar S} :
    v ∈ wtFormSubmodule hsym ↔ wtConj hsym v = v := by
  constructor
  · intro hv
    replace hv : ∀ σ : (Qi : Type) ≃ₐ[ℚ] (Qi : Type),
        (if σ = 1 then v else wtConj hsym v) = v := hv
    have h2 := hv galConj
    rwa [if_neg galConj_ne_one] at h2
  · intro hv
    show ∀ σ : (Qi : Type) ≃ₐ[ℚ] (Qi : Type), (if σ = 1 then v else wtConj hsym v) = v
    intro σ
    by_cases hσ : σ = 1
    · rw [if_pos hσ]
    · rw [if_neg hσ]; exact hv

open scoped Classical in
/-- **`baseChange`**: `ℚ[√-1] ⊗_ℚ M^{Gal} ≃ M`, S0's descent counit, an isomorphism by
`RQ-1.13` (`Descent.descentCounit_bijective`).  @census none (helper) -/
noncomputable def wtBaseChange (hsym : WtSymm S) :
    ((Qi : Type) ⊗[ℚ] ↥(wtFormSubmodule hsym)) ≃ₗ[(Qi : Type)] WtCar S :=
  LinearEquiv.ofBijective (Descent.descentCounit ℚ (Qi : Type) (wtVecK hsym))
    (Descent.descentCounit_bijective ℚ (Qi : Type) (wtVecK hsym))

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
theorem wtBaseChange_one_tmul (hsym : WtSymm S) (v : ↥(wtFormSubmodule hsym)) :
    wtBaseChange hsym ((1 : (Qi : Type)) ⊗ₜ[ℚ] v) = (v : WtCar S) := by
  show Descent.descentCounit ℚ (Qi : Type) (wtVecK hsym) ((1 : (Qi : Type)) ⊗ₜ[ℚ] v) = _
  rw [Descent.descentCounit_tmul, one_smul]

/-! ## `c` against the grading and the triple (`RQ-3.10-C3`) -/

theorem wtConj_comp (hsym : WtSymm S) (n : ℤ) (v : WtCar S) (hv : v ∈ wtComp S n) :
    wtConj hsym v ∈ wtComp S (-n) := by
  by_cases hn : S n
  · obtain ⟨a, rfl⟩ := exists_single_of_mem_wtComp (S := S) hn hv
    rw [wtConj_single]
    exact single_mem_wtComp (wtNeg hsym ⟨n, hn⟩) _
  · rw [eq_zero_of_mem_wtComp_not_mem (S := S) hn hv, map_zero]
    exact Submodule.zero_mem _

theorem wtConj_X (hsym : WtSymm S) (v : WtCar S) :
    wtConj hsym (wtX S x v) = wtY S x (wtConj hsym v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i a =>
      by_cases h : S ((i : ℤ) + 2)
      · have hjX : ((⟨(i : ℤ) + 2, h⟩ : WtIdx S) : ℤ) = ((i : ℤ)) + 2 := rfl
        have hjY : ((wtNeg hsym ⟨(i : ℤ) + 2, h⟩ : WtIdx S) : ℤ)
            = ((wtNeg hsym i : WtIdx S) : ℤ) - 2 := by
          simp only [wtNeg_val]; ring
        rw [wtX_single_eq hjX, wtConj_single, wtConj_single, wtY_single_eq hjY, wtNeg_val,
          map_mul, map_ratCast, neg_neg]
      · have h' : ¬ S (((wtNeg hsym i : WtIdx S) : ℤ) - 2) := by
          intro hc
          have heq : -(((wtNeg hsym i : WtIdx S) : ℤ) - 2) = (i : ℤ) + 2 := by
            rw [wtNeg_val]; ring
          exact h (heq ▸ hsym _ hc)
        rw [wtX_single_eq_zero h, map_zero, wtConj_single, wtY_single_eq_zero h']

theorem wtConj_Y (hsym : WtSymm S) (v : WtCar S) :
    wtConj hsym (wtY S x v) = wtX S x (wtConj hsym v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single i a =>
      by_cases h : S ((i : ℤ) - 2)
      · have hjY : ((⟨(i : ℤ) - 2, h⟩ : WtIdx S) : ℤ) = ((i : ℤ)) - 2 := rfl
        have hjX : ((wtNeg hsym ⟨(i : ℤ) - 2, h⟩ : WtIdx S) : ℤ)
            = ((wtNeg hsym i : WtIdx S) : ℤ) + 2 := by
          simp only [wtNeg_val]; ring
        rw [wtY_single_eq hjY, wtConj_single, wtConj_single, wtX_single_eq hjX, wtNeg_val,
          map_mul, map_ratCast]
      · have h' : ¬ S (((wtNeg hsym i : WtIdx S) : ℤ) + 2) := by
          intro hc
          have heq : -(((wtNeg hsym i : WtIdx S) : ℤ) + 2) = (i : ℤ) - 2 := by
            rw [wtNeg_val]; ring
          exact h (heq ▸ hsym _ hc)
        rw [wtY_single_eq_zero h, map_zero, wtConj_single, wtX_single_eq_zero h']

theorem wtConj_H (hsym : WtSymm S) (v : WtCar S) :
    wtConj hsym (wtH S v) = -wtH S (wtConj hsym v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg, neg_add]
  | single i a =>
      rw [wtH_single, wtConj_single, wtConj_single, wtH_single, wtNeg_val, ← Finsupp.single_neg,
        map_mul, map_intCast]
      congr 1
      push_cast
      ring

/-! ## The `§3.4` standing setup, the admissibility and the central character -/

/-- **The `§3.4` standing setup** carried by `(S, x)`: the engine datum `RationalSetupOver` over
`SqrtNegOneExt.qi` (the descent-presented `§3.4` datum), with the `ℚ`-form supplied by Galois
descent.  @census none (helper) -/
noncomputable def wtSetup (ℓ : ℕ) (S : ℤ → Prop) [DecidablePred S] (x : ℤ → ℚ)
    (hrel : WtSl2 S x) (hcas : WtCas ℓ S x) (hsym : WtSymm S) :
    RationalSetupOver ℓ ℚ SqrtNegOneExt.qi (↥(wtFormSubmodule hsym)) (WtCar S) where
  baseChange := wtBaseChange hsym
  weight := wtWeight S x hrel
  gic := wtGIC ℓ hrel hcas
  conj := wtConj hsym
  conj_smul a v := by rw [qi_conj]; exact wtConj_smul hsym a v
  conj_involutive := wtConj_involutive hsym
  conj_baseChange v := by
    show wtConj hsym (wtBaseChange hsym ((1 : (Qi : Type)) ⊗ₜ[ℚ] v))
      = wtBaseChange hsym ((1 : (Qi : Type)) ⊗ₜ[ℚ] v)
    rw [wtBaseChange_one_tmul]
    exact (mem_wtFormSubmodule hsym).mp v.2
  conj_comp := wtConj_comp hsym
  conj_X := wtConj_X hsym
  conj_Y := wtConj_Y hsym
  conj_H := wtConj_H hsym

@[simp] theorem wtSetup_weight (ℓ : ℕ) (hrel : WtSl2 S x) (hcas : WtCas ℓ S x) (hsym : WtSymm S) :
    (wtSetup ℓ S x hrel hcas hsym).weight = wtWeight S x hrel := rfl

@[simp] theorem wtSetup_conj (ℓ : ℕ) (hrel : WtSl2 S x) (hcas : WtCas ℓ S x) (hsym : WtSymm S) :
    (wtSetup ℓ S x hrel hcas hsym).conj = wtConj hsym := rfl

/-- Admissibility (`RQ-3.11-C2`): every weight space is at most one-dimensional, hence finite.
@census none (helper) -/
theorem wtAdmissible (n : ℤ) : FiniteDimensional (Qi : Type) (wtComp S n) := by
  by_cases hn : S n
  · rw [wtComp_of_mem hn]
    exact Module.Finite.range _
  · rw [wtComp_of_not_mem hn]
    infer_instance

/-- The central character (`RQ-3.03-C3`): `M_n = 0` unless `n ≡ ℓ - 1 (mod 2)`.
@census none (helper) -/
theorem wtCentralCharacter (ℓ : ℕ) (hpar : WtPar ℓ S) (n : ℤ)
    (hn : (n - ((ℓ : ℤ) - 1)) % 2 ≠ 0) : wtComp S n = ⊥ :=
  wtComp_of_not_mem fun hs => hn (hpar n hs)

/-! ## Finite generation -/

/-- A submodule containing every basis vector is everything.  @census none (helper) -/
theorem wtTop_of_single (N : Submodule (Qi : Type) (WtCar S))
    (h : ∀ i : WtIdx S, Finsupp.single i (1 : (Qi : Type)) ∈ N) : N = ⊤ := by
  have key : ∀ v : WtCar S, v ∈ N := by
    intro v
    induction v using Finsupp.induction_linear with
    | zero => exact N.zero_mem
    | add f g hf hg => exact N.add_mem hf hg
    | single i a =>
        have hm := N.smul_mem a (h i)
        rwa [Finsupp.smul_single, smul_eq_mul, mul_one] at hm
  exact eq_top_iff.2 fun v _ => key v

/-- Finite generation from a finite generating set, once one knows that every basis vector lies in
every `(𝔤,K)`-submodule containing it.  @census none (helper) -/
theorem wtIsFG (hrel : WtSl2 S x) (G : Finset (WtCar S))
    (h : ∀ N : Submodule (Qi : Type) (WtCar S), (↑G : Set (WtCar S)) ⊆ (N : Set (WtCar S)) →
      (wtWeight S x hrel).OpStable N → (wtWeight S x hrel).IsHomog N →
      ∀ i : WtIdx S, Finsupp.single i (1 : (Qi : Type)) ∈ N) :
    (wtWeight S x hrel).IsFG :=
  ⟨G, gkSpanGraded_eq_top _ fun N hN hop hhom => wtTop_of_single N (h N hN hop hhom)⟩

/-! ## The object of `HC_λ(𝔤,K)_ℚ` -/

/-- **The object of `HC_λ(𝔤,K)_ℚ` in the engine's presentation** (`HCEObj ℓ ℚ SqrtNegOneExt.qi`)
built from `(S, x)`.  @census none (helper) -/
noncomputable def wtHCEObj (ℓ : ℕ) (S : ℤ → Prop) [DecidablePred S] (x : ℤ → ℚ)
    (hrel : WtSl2 S x) (hcas : WtCas ℓ S x) (hsym : WtSymm S) (hpar : WtPar ℓ S)
    (hfg : (wtWeight S x hrel).IsFG) : HCEObj.{0} ℓ ℚ SqrtNegOneExt.qi where
  form := ↥(wtFormSubmodule hsym)
  carrier := WtCar S
  setup := wtSetup ℓ S x hrel hcas hsym
  admissible n := wtAdmissible n
  centralCharacter := wtCentralCharacter ℓ hpar
  fg := hfg

/-- **The object of `HC_λ(𝔤,K)_ℚ`** built from `(S, x)`: `§6`'s three examples are its
instantiations.  It is an object of `HC ℓ ℚ ImagUnit.qi` (`def:HClambdaE`, descent presentation),
obtained from `wtHCEObj` through the `R-V2-3` bridge `HCEObj.toHC`.  @census none (helper) -/
noncomputable def wtHC (ℓ : ℕ) (S : ℤ → Prop) [DecidablePred S] (x : ℤ → ℚ)
    (hrel : WtSl2 S x) (hcas : WtCas ℓ S x) (hsym : WtSymm S) (hpar : WtPar ℓ S)
    (hfg : (wtWeight S x hrel).IsFG) : HC ℓ ℚ ImagUnit.qi :=
  HCEObj.toHC (D := ImagUnit.qi) (h := Species.hcQ) (wtHCEObj ℓ S x hrel hcas hsym hpar hfg)

@[simp] theorem wtHC_carrier (ℓ : ℕ) (hrel : WtSl2 S x) (hcas : WtCas ℓ S x)
    (hsym : WtSymm S) (hpar : WtPar ℓ S) (hfg : (wtWeight S x hrel).IsFG) :
    (wtHC ℓ S x hrel hcas hsym hpar hfg).carrier = WtCar S := rfl

@[simp] theorem wtHC_weight (ℓ : ℕ) (hrel : WtSl2 S x) (hcas : WtCas ℓ S x)
    (hsym : WtSymm S) (hpar : WtPar ℓ S) (hfg : (wtWeight S x hrel).IsFG) :
    (wtHC ℓ S x hrel hcas hsym hpar hfg).weight = wtWeight S x hrel := rfl

/-- The carrier of an object of `HC ℓ ℚ ImagUnit.qi` is a `ℚ[√-1]`-space (`ImagUnit.qi.L` is
`Qi` by definition; instance search does not unfold it).  @census none (helper) -/
noncomputable instance instModuleQiHC {ℓ : ℕ} (A : HC ℓ ℚ ImagUnit.qi) :
    Module (Qi : Type) A.carrier := A.module

/-- The weight datum of an object of `HC ℓ ℚ ImagUnit.qi`, as the `Split.QiSetup` that §5.1's
construction consumes.  @census none (helper) -/
abbrev qiSetupOf {ℓ : ℕ} (A : HC ℓ ℚ ImagUnit.qi) : Split.QiSetup (Qi : Type) ℓ A.carrier :=
  ⟨A.weight, A.gic⟩

/-- **A morphism of `HC_λ(𝔤,K)_ℚ` from its `c`-compatibility alone.**  A `ℚ[√-1]`-linear map
commuting with `H, X, Y`, the grading and `c = galConj` commutes with every `σ ∈ Gal(ℚ[√-1]/ℚ)`
(`σ = 1` is trivial, every other `σ` is `c`): this is `HC.Hom`'s `map_gal`, and it is what the old
S8's `HCQHom` (v1) recorded as `map_conj`.  @census none (helper) -/
noncomputable def wtHomOf {ℓ : ℕ} {A B : HC ℓ ℚ ImagUnit.qi}
    (f : A.carrier →ₗ[(Qi : Type)] B.carrier)
    (map_H : ∀ v, f (A.weight.H v) = B.weight.H (f v))
    (map_X : ∀ v, f (A.weight.X v) = B.weight.X (f v))
    (map_Y : ∀ v, f (A.weight.Y v) = B.weight.Y (f v))
    (map_comp : ∀ (n : ℤ) (v : A.carrier), v ∈ A.weight.comp n → f v ∈ B.weight.comp n)
    (map_conj : ∀ v, f (A.galAct galConj v) = B.galAct galConj (f v)) : A ⟶ B :=
  HC.Hom.mk f map_H map_X map_Y map_comp (fun σ v => by
    rcases ImagUnit.qi.chi_cases σ with hσ | hσ
    · rw [HC.galAct_of_chi_one _ hσ, HC.galAct_of_chi_one _ hσ]
    · have hc : ImagUnit.qi.chi galConj = -1 :=
        ImagUnit.qi.chi_eq_neg_one_iff_ne_one.mpr galConj_ne_one
      rw [ImagUnit.qi.eq_of_chi_neg_one hσ hc]
      exact map_conj v)

/-- The conjugation of an example object is the Galois action of `c`.  @census none (helper) -/
theorem wtHC_galAct_conj (ℓ : ℕ) (hrel : WtSl2 S x) (hcas : WtCas ℓ S x)
    (hsym : WtSymm S) (hpar : WtPar ℓ S) (hfg : (wtWeight S x hrel).IsFG)
    {σ : ImagUnit.qi.L ≃ₐ[ℚ] ImagUnit.qi.L} (hσ : ImagUnit.qi.chi σ = -1) (v : WtCar S) :
    (wtHC ℓ S x hrel hcas hsym hpar hfg).galAct σ v = wtConj hsym v :=
  HCEObj.toHC_galAct_neg (D := ImagUnit.qi) (h := Species.hcQ)
    (wtHCEObj ℓ S x hrel hcas hsym hpar hfg) hσ v

/-- `c = galConj` acts on an example object as the coordinatewise conjugation `wtConj`.
@census none (helper) -/
theorem wtHC_galAct_galConj (ℓ : ℕ) (hrel : WtSl2 S x) (hcas : WtCas ℓ S x)
    (hsym : WtSymm S) (hpar : WtPar ℓ S) (hfg : (wtWeight S x hrel).IsFG) (v : WtCar S) :
    (wtHC ℓ S x hrel hcas hsym hpar hfg).galAct galConj v = wtConj hsym v :=
  wtHC_galAct_conj ℓ hrel hcas hsym hpar hfg
    (ImagUnit.qi.chi_eq_neg_one_iff_ne_one.mpr galConj_ne_one) v

/-! ## Weight-space dimensions, and reachability along the `𝔰𝔩₂`-string -/

/-- Every weight space in the support is **one**-dimensional (the `§6` K-type claims).
@census none (helper) -/
theorem wtComp_finrank {n : ℤ} (h : S n) :
    Module.finrank (Qi : Type) ↥(wtComp S n) = 1 := by
  rw [wtComp_of_mem h]
  have hinj : Function.Injective
      (Finsupp.lsingle (R := (Qi : Type)) (M := (Qi : Type)) (⟨n, h⟩ : WtIdx S)) :=
    Finsupp.single_injective (M := (Qi : Type)) (⟨n, h⟩ : WtIdx S)
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_self]

/-- A weight outside the support has zero weight space.  @census none (helper) -/
theorem wtComp_eq_bot {n : ℤ} (h : ¬ S n) : wtComp S n = ⊥ := wtComp_of_not_mem h

/-- One `Y`-step down inside a `(𝔤,K)`-submodule.  @census none (helper) -/
theorem wtStepDown (hrel : WtSl2 S x) {N : Submodule (Qi : Type) (WtCar S)}
    (hop : (wtWeight S x hrel).OpStable N) {i j : WtIdx S} (hj : (j : ℤ) = (i : ℤ) - 2)
    (hx : x (-(i : ℤ)) ≠ 0) (hi : Finsupp.single i (1 : (Qi : Type)) ∈ N) :
    Finsupp.single j (1 : (Qi : Type)) ∈ N := by
  have hY : wtY S x (Finsupp.single i (1 : (Qi : Type)))
      = Finsupp.single j ((x (-(i : ℤ)) : (Qi : Type))) := by
    rw [wtY_single_eq hj, mul_one]
  have hmem : Finsupp.single j ((x (-(i : ℤ)) : (Qi : Type))) ∈ N := hY ▸ hop.2.2 _ hi
  have hne : ((x (-(i : ℤ)) : ℚ) : (Qi : Type)) ≠ 0 := by
    simpa using hx
  have := N.smul_mem (((x (-(i : ℤ)) : ℚ) : (Qi : Type))⁻¹) hmem
  rwa [Finsupp.smul_single, smul_eq_mul, inv_mul_cancel₀ hne] at this

/-- One `X`-step up inside a `(𝔤,K)`-submodule.  @census none (helper) -/
theorem wtStepUp (hrel : WtSl2 S x) {N : Submodule (Qi : Type) (WtCar S)}
    (hop : (wtWeight S x hrel).OpStable N) {i j : WtIdx S} (hj : (j : ℤ) = (i : ℤ) + 2)
    (hx : x (i : ℤ) ≠ 0) (hi : Finsupp.single i (1 : (Qi : Type)) ∈ N) :
    Finsupp.single j (1 : (Qi : Type)) ∈ N := by
  have hX : wtX S x (Finsupp.single i (1 : (Qi : Type)))
      = Finsupp.single j ((x (i : ℤ) : (Qi : Type))) := by
    rw [wtX_single_eq hj, mul_one]
  have hmem : Finsupp.single j ((x (i : ℤ) : (Qi : Type))) ∈ N := hX ▸ hop.2.1 _ hi
  have hne : ((x (i : ℤ) : ℚ) : (Qi : Type)) ≠ 0 := by simpa using hx
  have := N.smul_mem (((x (i : ℤ) : ℚ) : (Qi : Type))⁻¹) hmem
  rwa [Finsupp.smul_single, smul_eq_mul, inv_mul_cancel₀ hne] at this

/-- `k` `Y`-steps down from a generator.  @census none (helper) -/
theorem wtChainDown (hrel : WtSl2 S x) {N : Submodule (Qi : Type) (WtCar S)}
    (hop : (wtWeight S x hrel).OpStable N) (b : ℤ) (hb : S b)
    (hgen : Finsupp.single (⟨b, hb⟩ : WtIdx S) (1 : (Qi : Type)) ∈ N) :
    ∀ (k : ℕ) (hk : ∀ j : ℕ, j < k → x (-(b - 2 * (j : ℤ))) ≠ 0)
      (hS : ∀ j : ℕ, j ≤ k → S (b - 2 * (j : ℤ))),
      Finsupp.single (⟨b - 2 * (k : ℤ), hS k le_rfl⟩ : WtIdx S) (1 : (Qi : Type)) ∈ N := by
  intro k
  induction k with
  | zero =>
      intro _ hS
      have : (⟨b - 2 * ((0 : ℕ) : ℤ), hS 0 le_rfl⟩ : WtIdx S) = ⟨b, hb⟩ := by
        apply Subtype.ext; push_cast; ring
      rw [this]; exact hgen
  | succ k ih =>
      intro hk hS
      have hSk : ∀ j : ℕ, j ≤ k → S (b - 2 * (j : ℤ)) := fun j hj => hS j (Nat.le_succ_of_le hj)
      have hprev := ih (fun j hj => hk j (Nat.lt_succ_of_lt hj)) hSk
      refine wtStepDown hrel hop ?_ ?_ hprev
      · push_cast; ring
      · have := hk k (Nat.lt_succ_self k)
        simpa using this

/-- `k` `X`-steps up from a generator.  @census none (helper) -/
theorem wtChainUp (hrel : WtSl2 S x) {N : Submodule (Qi : Type) (WtCar S)}
    (hop : (wtWeight S x hrel).OpStable N) (b : ℤ) (hb : S b)
    (hgen : Finsupp.single (⟨b, hb⟩ : WtIdx S) (1 : (Qi : Type)) ∈ N) :
    ∀ (k : ℕ) (hk : ∀ j : ℕ, j < k → x (b + 2 * (j : ℤ)) ≠ 0)
      (hS : ∀ j : ℕ, j ≤ k → S (b + 2 * (j : ℤ))),
      Finsupp.single (⟨b + 2 * (k : ℤ), hS k le_rfl⟩ : WtIdx S) (1 : (Qi : Type)) ∈ N := by
  intro k
  induction k with
  | zero =>
      intro _ hS
      have : (⟨b + 2 * ((0 : ℕ) : ℤ), hS 0 le_rfl⟩ : WtIdx S) = ⟨b, hb⟩ := by
        apply Subtype.ext; push_cast; ring
      rw [this]; exact hgen
  | succ k ih =>
      intro hk hS
      have hSk : ∀ j : ℕ, j ≤ k → S (b + 2 * (j : ℤ)) := fun j hj => hS j (Nat.le_succ_of_le hj)
      have hprev := ih (fun j hj => hk j (Nat.lt_succ_of_lt hj)) hSk
      refine wtStepUp hrel hop ?_ ?_ hprev
      · push_cast; ring
      · have := hk k (Nat.lt_succ_self k)
        simpa using this

/-- The `Finset` of generators used by `wtIsFG`, for a single generator.
@census none (helper) -/
noncomputable def wtGen (i : WtIdx S) : Finset (WtCar S) :=
  {Finsupp.single i (1 : (Qi : Type))}

theorem wtGen_subset {i : WtIdx S} {N : Submodule (Qi : Type) (WtCar S)}
    (h : (↑(wtGen i) : Set (WtCar S)) ⊆ (N : Set (WtCar S))) :
    Finsupp.single i (1 : (Qi : Type)) ∈ N := h (by simp [wtGen])

/-- The `Finset` of generators used by `wtIsFG`, for two generators.  @census none (helper) -/
noncomputable def wtGen2 (i j : WtIdx S) : Finset (WtCar S) :=
  {Finsupp.single i (1 : (Qi : Type)), Finsupp.single j (1 : (Qi : Type))}

theorem wtGen2_subset_left {i j : WtIdx S} {N : Submodule (Qi : Type) (WtCar S)}
    (h : (↑(wtGen2 i j) : Set (WtCar S)) ⊆ (N : Set (WtCar S))) :
    Finsupp.single i (1 : (Qi : Type)) ∈ N := h (by simp [wtGen2])

theorem wtGen2_subset_right {i j : WtIdx S} {N : Submodule (Qi : Type) (WtCar S)}
    (h : (↑(wtGen2 i j) : Set (WtCar S)) ⊆ (N : Set (WtCar S))) :
    Finsupp.single j (1 : (Qi : Type)) ∈ N := h (by simp [wtGen2])

/-! ## G4 proof helpers

Added at G4 (2026-09-07, `s9-g4-impl`).  Neither carries a `@census` id or a `@clauses` list, so
neither is a claimant or a citer: `rqaudit coverage`/`clauses` are unmoved by them.  They exist
because the same two arguments are needed by `F_irreducible`, `D_irreducible`, `D_decomposition`
and the three `finrank` counts, and stating each once is what makes those proofs comparable — the
same reason `Basic.lean` itself exists (`DESIGN-NOTES.md` §2).
-/

/-- **A non-zero homogeneous `(𝔤,K)`-submodule contains a basis vector.**  This is what makes
irreducibility checkable on the weight line: `IsHomog` splits any non-zero element into weight
components, one of which is non-zero and hence a non-zero multiple of some `e_n`.
@census none (helper) -/
theorem wtExists_single_mem {N : Submodule (Qi : Type) (WtCar S)} (hrel : WtSl2 S x)
    (hhom : (wtWeight S x hrel).IsHomog N) (hN : N ≠ ⊥) :
    ∃ i : WtIdx S, Finsupp.single i (1 : (Qi : Type)) ∈ N := by
  obtain ⟨v, hvN, hv0⟩ := (Submodule.ne_bot_iff N).mp hN
  obtain ⟨t, -, hsum⟩ := (wtWeight S x hrel).exists_sum_proj v
  have hex : ∃ n ∈ t, (wtWeight S x hrel).proj n v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv0 (by rw [← hsum]; exact Finset.sum_eq_zero hcon)
  obtain ⟨n, -, hn⟩ := hex
  have hmemN : (wtWeight S x hrel).proj n v ∈ N := hhom n v hvN
  have hmemC : (wtWeight S x hrel).proj n v ∈ wtComp S n := (wtWeight S x hrel).proj_mem n v
  have hS : S n := by
    by_contra hS
    exact hn (eq_zero_of_mem_wtComp_not_mem (S := S) hS hmemC)
  obtain ⟨a, ha⟩ := exists_single_of_mem_wtComp (S := S) hS hmemC
  have ha0 : a ≠ 0 := by
    intro h0
    exact hn (by rw [ha, h0, Finsupp.single_zero])
  refine ⟨⟨n, hS⟩, ?_⟩
  have hsm := N.smul_mem a⁻¹ (ha ▸ hmemN)
  rwa [Finsupp.smul_single, smul_eq_mul, inv_mul_cancel₀ ha0] at hsm

/-- **The dimension of `M` is the size of its support**, read off any enumeration of the support
by `Fin k`.  `M = ⨁_{n ∈ S} ℚ[√-1]·e_n` is `WtIdx S →₀ ℚ[√-1]`, so this is
`Module.finrank_finsupp_self` transported along `e`.  @census none (helper) -/
theorem wtFinrank_of_equiv {k : ℕ} (e : WtIdx S ≃ Fin k) :
    Module.finrank (Qi : Type) (WtCar S) = k := by
  have hlin : (WtCar S) ≃ₗ[(Qi : Type)] (Fin k →₀ (Qi : Type)) :=
    Finsupp.domLCongr (M := (Qi : Type)) e
  rw [hlin.finrank_eq, Module.finrank_finsupp_self, Fintype.card_fin]

/-- **`∏_{j<m}(c - (k-2j)²)` when `C` is the scalar `c = ℓ²`.**  `casimirFactorProd` is a product
of polynomials in `C`; on an object where `C` **is** a scalar (design decision `D-S9-3`,
`wtCasimir_eq`) every factor is a scalar, and the product is `nilpScalar` — the very scalar S7
divides out.  @census none (helper) -/
theorem casimirFactorProd_scalar {E : Type*} [Field E] {M : Type*} [AddCommGroup M] [Module E M]
    (ℓ : ℕ) (k : ℤ) (m : ℕ) :
    casimirFactorProd (((ℓ : E) ^ 2) • (1 : Module.End E M)) k m
      = (nilpScalar ℓ k m E) • (1 : Module.End E M) := by
  induction m generalizing k with
  | zero => rw [casimirFactorProd_zero, nilpScalar_zero, one_smul]
  | succ m ih =>
      rw [casimirFactorProd_succ, ih, nilpScalar_succ, ← sub_smul, smul_mul_smul_comm, one_mul]

/-- **The unipotent stabilization `T₋` is the identity when `C` is the scalar `ℓ²`.**  This is
what makes `RQ2-6.01-C7`'s "`Y_⋆ ∘ X_⋆` is already the identity", `RQ2-6.02-C6`'s `T₋ = 𝟏` and
`RQ2-6.03-C5` true at all four of `§6`'s objects at once: `qiRemainder` is by construction
`casimirFactorProd C (ℓ-2) (ℓ-1)` minus the scalar S7 normalizes by, and at a scalar Casimir the
two agree, so the remainder vanishes identically rather than merely nilpotently.
@census none (helper) -/
theorem tMinus_eq_one_of_casimir_scalar {ℓ : ℕ} {Mi : Type} [AddCommGroup Mi]
    [Module (Qi : Type) Mi] (Q : Split.QiSetup (Qi : Type) ℓ Mi) (hℓ : 1 ≤ ℓ)
    (hc : Q.weight.casimir = (algebraMap ℚ (Qi : Type) ((ℓ : ℚ) ^ 2)) • 1) (v : Mi) :
    Split.tMinus Q v = v := by
  have halg : (algebraMap ℚ (Qi : Type)) ((ℓ : ℚ) ^ 2) = ((ℓ : (Qi : Type)) ^ 2) := by
    rw [map_pow, map_natCast]
  have hrem : Split.qiRemainder Q = 0 := by
    rw [Split.qiRemainder, hc, halg, casimirFactorProd_scalar, sub_self, smul_zero]
  rw [Split.tMinus_apply' Q hℓ v, hrem]
  simp

/-- **Hilbert 90 by hand at a `c`-fixed vertex.**  A `c`-semi-linear involution of a non-zero
`ℚ[√-1]`-space has a non-zero fixed vector: either `e + φe ≠ 0`, or `φe = -e` and `i·e` is fixed.
This is the verifier's probe `P4` (`VERIFICATION.md` §7), and it is why the four `∃ b ≠ 0`
conjuncts pin the display's isomorphism class and no more (finding `V-S9G2-2`).
@census none (helper) -/
theorem exists_fixed_ne_zero {V : Type} [AddCommGroup V] [Module (Qi : Type) V] {e : V}
    (he : e ≠ 0) (φ : V ≃+ V)
    (hsemi : ∀ (a : (Qi : Type)) (v : V), φ (a • v) = galConj a • φ v)
    (hinv : ∀ v, φ (φ v) = v) : ∃ b : V, b ≠ 0 ∧ φ b = b := by
  by_cases h : e + φ e = 0
  · have hφe : φ e = -e := by rw [← neg_eq_of_add_eq_zero_right h]
    obtain ⟨a, ha⟩ : ∃ a : (Qi : Type), galConj a ≠ a := by
      by_contra hcon
      push_neg at hcon
      exact galConj_ne_one (AlgEquiv.ext hcon)
    set i : (Qi : Type) := a - galConj a with hi
    have hci : galConj i = -i := by rw [hi, map_sub, galConj_galConj]; ring
    have hine : i ≠ 0 := by
      intro h0; apply ha; rw [hi] at h0; exact (sub_eq_zero.mp h0).symm
    exact ⟨i • e, smul_ne_zero hine he, by rw [hsemi, hci, hφe, neg_smul, smul_neg, neg_neg]⟩
  · exact ⟨e + φ e, h, by rw [map_add, hinv, add_comm]⟩

/-- **A non-zero vector has non-zero image under an additive equivalence.**  The `D`-shaped
`∃ b ≠ 0 ∧ φ b ≠ 0` conjunct (verifier probe `P3`).  @census none (helper) -/
theorem exists_ne_zero_map_ne_zero {V W : Type} [AddCommGroup V] [AddCommGroup W] {e : V}
    (he : e ≠ 0) (φ : V ≃+ W) : ∃ b : V, b ≠ 0 ∧ φ b ≠ 0 :=
  ⟨e, he, fun h => he (φ.injective (by rw [h, map_zero]))⟩

/-- `c` read coefficientwise: `(c·v)_j = c(v_{-j})`.  @census none (helper) -/
theorem wtConj_apply (hsym : WtSymm S) (v : WtCar S) (j : WtIdx S) :
    wtConj hsym v j = galConj (v (wtNeg hsym j)) := rfl

/-- `wtNeg` is an involution.  @census none (helper) -/
@[simp] theorem wtNeg_wtNeg (hsym : WtSymm S) (i : WtIdx S) :
    wtNeg hsym (wtNeg hsym i) = i := Subtype.ext (neg_neg _)

/-- **A subspace cut out by a set of weights is a `(𝔤,K)`-submodule**, provided each `X`- and
`Y`-step out of the set either lands back in it or has vanishing scalar.  This is what makes
`§6.2`'s splitting `D_ℓ = D_ℓ⁺ ⊕ D_ℓ⁻` expressible: the two half-strings are `Finsupp.supported`
at the positive and the negative weights, and the only step that leaves the positive half is the
one across the gap, whose scalar is the wall's `0`.  @census none (helper) -/
theorem wtSupported_opStable (hrel : WtSl2 S x) (T : Set (WtIdx S))
    (hX : ∀ i ∈ T, ∀ j : WtIdx S, (j : ℤ) = (i : ℤ) + 2 → j ∈ T ∨ x (i : ℤ) = 0)
    (hY : ∀ i ∈ T, ∀ j : WtIdx S, (j : ℤ) = (i : ℤ) - 2 → j ∈ T ∨ x (-(i : ℤ)) = 0) :
    (wtWeight S x hrel).OpStable (Finsupp.supported (Qi : Type) (Qi : Type) T) := by
  have key : ∀ f : Module.End (Qi : Type) (WtCar S),
      (∀ i ∈ T, f (Finsupp.single i (1 : (Qi : Type)))
        ∈ Finsupp.supported (Qi : Type) (Qi : Type) T) →
      ∀ v ∈ Finsupp.supported (Qi : Type) (Qi : Type) T,
        f v ∈ Finsupp.supported (Qi : Type) (Qi : Type) T := by
    intro f hf v hv
    have hle : Finsupp.supported (Qi : Type) (Qi : Type) T
        ≤ Submodule.comap f (Finsupp.supported (Qi : Type) (Qi : Type) T) := by
      conv_lhs => rw [Finsupp.supported_eq_span_single]
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact Submodule.mem_comap.mpr (hf i hi)
    exact hle hv
  refine ⟨key _ ?_, key _ ?_, key _ ?_⟩
  · intro i hi
    rw [wtWeight_H, wtH_single]
    exact Finsupp.single_mem_supported _ _ hi
  · intro i hi
    rw [wtWeight_X, wtX_single]
    by_cases h : S ((i : ℤ) + 2)
    · rw [dif_pos h]
      rcases hX i hi ⟨(i : ℤ) + 2, h⟩ rfl with hj | hx0
      · exact Finsupp.single_mem_supported _ _ hj
      · rw [hx0]; simp
    · rw [dif_neg h]; exact Submodule.zero_mem _
  · intro i hi
    rw [wtWeight_Y, wtY_single]
    by_cases h : S ((i : ℤ) - 2)
    · rw [dif_pos h]
      rcases hY i hi ⟨(i : ℤ) - 2, h⟩ rfl with hj | hx0
      · exact Finsupp.single_mem_supported _ _ hj
      · rw [hx0]; simp
    · rw [dif_neg h]; exact Submodule.zero_mem _

/-- **A subspace cut out by a set of weights is homogeneous**: it is spanned by basis vectors, and
the projection of a basis vector is either itself or `0`.  @census none (helper) -/
theorem wtSupported_isHomog (hrel : WtSl2 S x) (T : Set (WtIdx S)) :
    (wtWeight S x hrel).IsHomog (Finsupp.supported (Qi : Type) (Qi : Type) T) := by
  intro n v hv
  have hle : Finsupp.supported (Qi : Type) (Qi : Type) T
      ≤ Submodule.comap ((wtWeight S x hrel).proj n)
        (Finsupp.supported (Qi : Type) (Qi : Type) T) := by
    conv_lhs => rw [Finsupp.supported_eq_span_single]
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    refine Submodule.mem_comap.mpr ?_
    by_cases hin : (i : ℤ) = n
    · have hmem : Finsupp.single i (1 : (Qi : Type)) ∈ (wtWeight S x hrel).comp n := by
        rw [wtWeight_comp, ← hin]; exact single_mem_wtComp i 1
      rw [(wtWeight S x hrel).proj_of_mem_same hmem]
      exact Finsupp.single_mem_supported _ _ hi
    · rw [(wtWeight S x hrel).proj_of_mem_ne
        (show Finsupp.single i (1 : (Qi : Type)) ∈ (wtWeight S x hrel).comp (i : ℤ) from
          single_mem_wtComp i 1) hin]
      exact Submodule.zero_mem _
  exact hle hv

/-- **A map between two weight lines in the support is bijective as soon as it is injective**:
both are one-dimensional (`wtComp_finrank`) and finite (`wtAdmissible`).  @census none (helper) -/
theorem wtBijective_of_injective {n m : ℤ} (hn : S n) (hm : S m)
    {f : ↥(wtComp S n) →ₗ[(Qi : Type)] ↥(wtComp S m)} (hf : Function.Injective f) :
    Function.Bijective f := by
  haveI : FiniteDimensional (Qi : Type) ↥(wtComp S n) := wtAdmissible (S := S) n
  haveI : FiniteDimensional (Qi : Type) ↥(wtComp S m) := wtAdmissible (S := S) m
  have hdim : Module.finrank (Qi : Type) ↥(wtComp S n)
      = Module.finrank (Qi : Type) ↥(wtComp S m) := by
    rw [wtComp_finrank hn, wtComp_finrank hm]
  refine ⟨hf, ?_⟩
  have h := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := (Qi : Type)) (V := ↥(wtComp S n)) (V₂ := ↥(wtComp S m)) hdim (f := f)).mp hf
  exact h

/-- **An operator restricted to a weight line is injective when it kills no basis multiple.**
@census none (helper) -/
theorem wtRestrict_injective {n m : ℤ} (hn : S n) {f : Module.End (Qi : Type) (WtCar S)}
    (hf : ∀ v ∈ wtComp S n, f v ∈ wtComp S m)
    (hker : ∀ a : (Qi : Type), f (Finsupp.single (⟨n, hn⟩ : WtIdx S) a) = 0 → a = 0) :
    Function.Injective (f.restrict hf) := by
  intro u v huv
  obtain ⟨a, ha⟩ := exists_single_of_mem_wtComp (S := S) hn u.2
  obtain ⟨b, hb⟩ := exists_single_of_mem_wtComp (S := S) hn v.2
  have h := congrArg Subtype.val huv
  rw [LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply, ha, hb] at h
  have hsub : f (Finsupp.single (⟨n, hn⟩ : WtIdx S) (a - b)) = 0 := by
    rw [Finsupp.single_sub, map_sub, h, sub_self]
  exact Subtype.ext (by rw [ha, hb, sub_eq_zero.mp (hker _ hsub)])

/-- **A step along the weight line is bijective exactly when its scalar is non-zero.**  This is
what turns `§6.3`'s "the displayed map is an isomorphism" into a check on one rational number.
@census none (helper) -/
theorem wtRestrict_bijective_of_scalar {n m : ℤ} (hn : S n) (hm : S m)
    (f : Module.End (Qi : Type) (WtCar S)) (hf : ∀ v ∈ wtComp S n, f v ∈ wtComp S m)
    {c : (Qi : Type)} (hc : c ≠ 0)
    (hval : ∀ a : (Qi : Type),
      f (Finsupp.single (⟨n, hn⟩ : WtIdx S) a) = Finsupp.single (⟨m, hm⟩ : WtIdx S) (c * a)) :
    Function.Bijective (f.restrict hf) := by
  refine wtBijective_of_injective hn hm (wtRestrict_injective hn hf fun a hazero => ?_)
  rw [hval] at hazero
  have : c * a = 0 := Finsupp.single_injective (⟨m, hm⟩ : WtIdx S) (by rw [hazero]; simp)
  exact (mul_eq_zero.mp this).resolve_left hc

/-- **An operator restricted to a weight line is zero when it kills the basis vector.**
@census none (helper) -/
theorem wtRestrict_eq_zero {n m : ℤ} (hn : S n) {f : Module.End (Qi : Type) (WtCar S)}
    (hf : ∀ v ∈ wtComp S n, f v ∈ wtComp S m)
    (hzero : ∀ a : (Qi : Type), f (Finsupp.single (⟨n, hn⟩ : WtIdx S) a) = 0) :
    f.restrict hf = 0 := by
  refine LinearMap.ext fun u => Subtype.ext ?_
  obtain ⟨a, ha⟩ := exists_single_of_mem_wtComp (S := S) hn u.2
  rw [LinearMap.coe_restrict_apply, ha, hzero]
  rfl

/-- **A weight line in the support carries a non-zero vector.**  @census none (helper) -/
theorem wtComp_elt_ne_zero {n : ℤ} (hS : S n) :
    (⟨Finsupp.single (⟨n, hS⟩ : WtIdx S) (1 : (Qi : Type)),
        single_mem_wtComp (⟨n, hS⟩ : WtIdx S) 1⟩ : ↥(wtComp S n)) ≠ 0 := by
  intro h
  exact (Finsupp.single_ne_zero.mpr one_ne_zero) (congrArg Subtype.val h)

/-- **The module is non-trivial as soon as the support is.**  @census none (helper) -/
theorem wtBot_ne_top (i : WtIdx S) : (⊥ : Submodule (Qi : Type) (WtCar S)) ≠ ⊤ := by
  intro h
  have hmem : Finsupp.single i (1 : (Qi : Type)) ∈ (⊥ : Submodule (Qi : Type) (WtCar S)) := by
    rw [h]; trivial
  rw [Submodule.mem_bot] at hmem
  exact (Finsupp.single_ne_zero.mpr one_ne_zero) hmem

/-! ## The two comparison functors and the two species nodes, pinned

`§6`'s statements are about `𝔼_ℚ` and about `F`; both are pinned here to the tree's own
declarations (the native `E_E ℚ ImagUnit.qi ℓ` of T3, re-indexed to `Γ_ℚ` (`EQNat`, `ECycNat`), which is
isomorphic with identity components to the engine functors `Equivalence.E_QFunctor`/`Cyclic.E_CycFunctor`
precomposed with the `R-V2-3` bridge `Compat.toHCEObjFunctor` (`EQFun`, `ECycFun`), and S5's `FFunctor`), so that no `§6` statement quantifies over an
unconstrained functor.
-/

/-- `𝔼_ℚ : HC_λ(𝔤,K)_ℚ ⥤ Rep^nil(Γ_ℚ)` at `ℓ ≥ 1`, at the engine's own proved specification.
@census none (helper) -/
noncomputable abbrev EQFun {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    HC ℓ ℚ ImagUnit.qi ⥤ RepNilQ SqrtNegOneExt.qi.card_gal :=
  Compat.toHCEObjFunctor (ℓ := ℓ) Species.hcQ ⋙
    Equivalence.E_QFunctor SqrtNegOneExt.qi.card_gal hℓ (Equivalence.E_Q_spec SqrtNegOneExt.qi.card_gal hℓ)

/-- `𝔼_ℚ : HC_0(𝔤,K)_ℚ ⥤ Rep^nil(Γ_ℚ^cyc)` at `ℓ = 0`.  @census none (helper) -/
noncomputable abbrev ECycFun : HC 0 ℚ ImagUnit.qi ⥤ RepNilCycQ SqrtNegOneExt.qi.card_gal :=
  Compat.toHCEObjFunctor (ℓ := 0) Species.hcQ ⋙
    Cyclic.E_CycFunctor SqrtNegOneExt.qi.card_gal (Cyclic.E_Cyc_spec SqrtNegOneExt.qi.card_gal)

/-- The node `{⋆}` of the étale `ℚ`-species `S(Γ_ℚ)`.  @census none (helper) -/
noncomputable abbrev starNode : (gelfandQ SqrtNegOneExt.qi.card_gal).toSpecies.I :=
  (gelfandQ SqrtNegOneExt.qi.card_gal).vertexClass (vtxQ SqrtNegOneExt.qi.card_gal 1)

/-- The node `{+,−}` of the étale `ℚ`-species `S(Γ_ℚ)`.  @census none (helper) -/
noncomputable abbrev pmNode : (gelfandQ SqrtNegOneExt.qi.card_gal).toSpecies.I :=
  (gelfandQ SqrtNegOneExt.qi.card_gal).vertexClass (vtxQ SqrtNegOneExt.qi.card_gal 0)

/-- The single node of the étale `ℚ`-species of the cyclic quiver.  @census none (helper) -/
noncomputable abbrev cycNode : (cyclicQ SqrtNegOneExt.qi.card_gal).toSpecies.I :=
  (cyclicQ SqrtNegOneExt.qi.card_gal).vertexClass (vtxC SqrtNegOneExt.qi.card_gal 0)

/-! ## G4 species helpers — computing S5's `F` at a concrete representation

Added at G4 (2026-09-07, `s9-g4-impl`).  Nothing in the committed tree evaluated
`RationalQuiver.FFunctor` at a non-degenerate object before S9: the only in-tree instances were the
zero object's (`Gelfand/Models.lean`, deleted with the v1 Q-chain at WP-13, `ae9eda9`; 2026-10-21
note, O-V2-6 round 2), discharged by `Subsingleton.elim`.  So `§6`'s five
`…_speciesRep_eq` statements needed the computation to be **built**, not cited, and this section is
that build.  Every declaration here is `@census none`; none carries a `@clauses` list, so
`rqaudit coverage`/`clauses` are unmoved by them.

**Re-tensed 2026-09-12** (`R-PROC-4` round 4, coordinator ruling `R-ERR-4`).  The descent
formulas this section built are **S5 content**, and they are now *in* S5:
`lean/RationalQuivers/Species/Rep/GelfandDescent.lean` carries `edgeDescentOf_generator`,
`edgeDescentOf_uniqueOrbit`, `f_uniqueOrbit_generator` and `f_twoTerm_generator` — the last two
stated for an arbitrary `Γ` with the Gelfand-specific input (the stabilizer at the target, the
edge stabilizers) as a hypothesis — together with `rep_eq_one`, `cosetIndex_subsingleton`,
`phiComp_eq`, `phiComp_ne_zero`, `phiComp_split`, `wv`, `Ten`, `tmk`, `uPS` and
`gal_univ_of_card_two`.  `RQ-2.37`'s clause `C3` needs exactly those three formulas and could not
consume them here, S9 being downstream of S5 and S8 (`stages/S5/DESIGN-NOTES.md` §71.5).
**Every one of those names still exists in this file, with its type unchanged, as a thin alias**
— `tools/decl-regression.sh --stage S9 --baseline 5e46bb6` reports 0 MISSING and 0 CHANGED — so
the docstrings below still say what their declarations say; what they no longer say is where the
proof is.  The declarations this section still *proves* are the rest: the node computations, the
`finrank` facts, the edge-orbit computations for `Γ_ℚ`, and the two bijectivity/surjectivity
statements `species_star_pm_bijective` and `species_pm_star_surjective` that `§6` consumes.

Three things it establishes, each generic in the quiver and reusable:

* **which node is which** — `Γ_ℚ`'s two species nodes are `{⋆}` and `{±}` (`node_cases`), the
  `⋆`-orbit is a singleton so `vertexRep starNode = ⋆` on the nose, and the `±`-orbit's
  representative is one of the two `±` vertices;
* **`finrank_W`** — the `ℚ`-dimension of `W_i = M(v_i)^{G_{v_i}}` is
  `[L(v_i) : ℚ] · dim_{ℚ[√-1]} M(v_i)`, by Galois descent (`vertexDescentEquiv`), which is what
  turns `§6`'s "`W_⋆ = ℚ`, `W_± = ℚ[√-1]`" into the two weight-space dimensions already proved;
* **when a structure map `f_{i,j}` vanishes, and when it does not** — `edgeDescentOf` is
  choice-defined and must not be unfolded, so the handles are `Balanced.hom_ext` (a map out of a
  balanced product is pinned on generators) together with the edge-orbit computations for `Γ_ℚ`.
-/

section SpeciesG4

open MulAction

/- **Resource budgets, raised for this section only and disclosed rather than absorbed.**  Two
elaboration limits are raised here; both are *resource* limits, not soundness knobs, and the axiom
closure is unaffected (`rqaudit axioms --stage S9` is the check, and it reads the closure, not the
budget).  They are set inside `section SpeciesG4` so that every G2 construction and every other G4
proof in this stage keeps Lean's defaults.  (The same two budgets, for the same measured reason,
are raised inside `section Concrete` of S5's `Species/Rep/GelfandDescent.lean` since 2026-09-12;
they travelled with the relocated proofs.)

Measured, not precautionary: with both at their defaults the section fails with four
`failed to synthesize … synthInstance.maxHeartbeats` errors; with only `synthInstance` raised it
fails with a `(deterministic) timeout at isDefEq` at `finrank_vertexFixed`.  The hot spot in both
cases is the instance `Module ↥(stabField K L v) ↥(M.vertexFixed v)` — the fixed points of a
vertex space as a module over that vertex's stabilizer field — which no in-tree declaration had
needed before, because nothing in the tree had evaluated `FFunctor` at a non-degenerate object. -/
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

noncomputable abbrev GQ : RationalQuiver ℚ (Qi : Type) := gelfandQ SqrtNegOneExt.qi.card_gal

/-- Every species node of `Γ_ℚ` is `{⋆}` or `{±}`. -/
theorem node_cases : ∀ i : GQ.toSpecies.I, i = starNode ∨ i = pmNode := by
  have key : ∀ n : Fin 3, (GQ.vertexClass (vtxQ SqrtNegOneExt.qi.card_gal n) = starNode) ∨
      (GQ.vertexClass (vtxQ SqrtNegOneExt.qi.card_gal n) = pmNode) := by
    intro n
    fin_cases n
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact Or.inr (RationalQuivers.Examples.gelfand_vertexClass_two ℚ (Qi : Type) Qi.card_gal)
  exact Quotient.ind fun v => key v

theorem star_ne_pm : (starNode : GQ.toSpecies.I) ≠ pmNode :=
  RationalQuivers.Examples.gelfand_vertexClass_star_ne ℚ (Qi : Type) Qi.card_gal

set_option backward.isDefEq.respectTransparency.types false in
/-- `c` acts on the vertices of `Γ_ℚ` by the `±`-swap, `c = galConj`.  @census none (helper) -/
theorem gelfandQ_smul_vertex (v : Fin 3) :
    galConj • vtxQ SqrtNegOneExt.qi.card_gal v
      = vtxQ SqrtNegOneExt.qi.card_gal (RQuiver.gelfandVertexSwap v) := by
  rw [← qi_conj]; exact RationalStructure.gelfandQ_smul_vertex _ v

set_option backward.isDefEq.respectTransparency.types false in
/-- `c` acts on the edges of `Γ_ℚ` by the `±`-swap, `c = galConj`.  @census none (helper) -/
theorem gelfandQ_smul_edge (e : Fin 4) :
    galConj • edgeQ SqrtNegOneExt.qi.card_gal e
      = edgeQ SqrtNegOneExt.qi.card_gal (RQuiver.gelfandEdgeSwap e) := by
  rw [← qi_conj]; exact RationalStructure.gelfandQ_smul_edge _ e

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- `σ • v` on `Γ_ℚ`, computed: `v` for `σ = 1`, the swap otherwise.  @census none (helper) -/
theorem gelfandQ_smul_eq (σ : (Qi : Type) ≃ₐ[ℚ] (Qi : Type)) (v : Fin 3) :
    σ • vtxQ SqrtNegOneExt.qi.card_gal v
      = vtxQ SqrtNegOneExt.qi.card_gal (if σ = 1 then v else RQuiver.gelfandVertexSwap v) := by
  by_cases hσ : σ = 1
  · subst hσ; simp [vtxQ]
  · rw [if_neg hσ, eq_galConj_of_ne_one Qi.card_gal hσ, gelfandQ_smul_vertex]

set_option backward.isDefEq.respectTransparency.types false in
/-- `c` acts on the edges of the cyclic quiver by the swap, `c = galConj`.  @census none (helper) -/
theorem cyclicQ_smul_edge (e : Fin 2) :
    galConj • edgeC SqrtNegOneExt.qi.card_gal e
      = edgeC SqrtNegOneExt.qi.card_gal (RQuiver.twoLoopsSwapPerm e) := by
  rw [← qi_conj]; exact Cyclic.cyclicQ_smul_edge _ e

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- `σ • v` on the cyclic quiver, computed.  @census none (helper) -/
theorem cyclicQ_smul_eq (σ : (Qi : Type) ≃ₐ[ℚ] (Qi : Type)) (v : Fin 2) :
    σ • vtxC SqrtNegOneExt.qi.card_gal v
      = vtxC SqrtNegOneExt.qi.card_gal (if σ = 1 then v else RQuiver.twoLoopsSwapPerm v) :=
  Cyclic.cyclicQ_smul_eq SqrtNegOneExt.qi.card_gal σ v

set_option backward.isDefEq.respectTransparency.types false in
theorem galConj_fix_star : galConj • vtxQ SqrtNegOneExt.qi.card_gal 1 = vtxQ SqrtNegOneExt.qi.card_gal 1 := by
  rw [gelfandQ_smul_vertex]; rfl

/-- The chosen representative of `{⋆}` is `⋆`. -/
theorem vertexRep_starNode : GQ.vertexRep starNode = vtxQ SqrtNegOneExt.qi.card_gal 1 := by
  obtain ⟨σ, hσ⟩ := mem_orbit_iff.mp (GQ.mem_orbit_vertexRep (vtxQ SqrtNegOneExt.qi.card_gal 1))
  by_cases hne : σ = 1
  · rw [hne, one_smul] at hσ; exact hσ
  · rw [eq_galConj_of_ne_one Qi.card_gal hne] at hσ
    exact MulAction.injective galConj (hσ.trans galConj_fix_star.symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- The chosen representative of `{±}` is `−` or `+`. -/
theorem vertexRep_pmNode :
    GQ.vertexRep pmNode = vtxQ SqrtNegOneExt.qi.card_gal 0 ∨ GQ.vertexRep pmNode = vtxQ SqrtNegOneExt.qi.card_gal 2 := by
  obtain ⟨σ, hσ⟩ := mem_orbit_iff.mp (GQ.mem_orbit_vertexRep (vtxQ SqrtNegOneExt.qi.card_gal 0))
  by_cases hne : σ = 1
  · rw [hne, one_smul] at hσ; exact Or.inl hσ
  · rw [eq_galConj_of_ne_one Qi.card_gal hne] at hσ
    refine Or.inr ?_
    have h2 : galConj • vtxQ SqrtNegOneExt.qi.card_gal 2 = vtxQ SqrtNegOneExt.qi.card_gal 0 := by
      rw [gelfandQ_smul_vertex]; rfl
    exact MulAction.injective galConj (hσ.trans h2.symm)

theorem stabField_star : stabField ℚ (Qi : Type) (GQ.vertexRep starNode) = ⊥ :=
  RationalQuivers.Examples.gelfand_vertexOrbitField_star ℚ (Qi : Type) Qi.card_gal

theorem stabField_pm : stabField ℚ (Qi : Type) (GQ.vertexRep pmNode) = ⊤ :=
  RationalQuivers.Examples.gelfand_vertexOrbitField_pm ℚ (Qi : Type) Qi.card_gal

section Finrank

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  {Γ : RationalQuiver K L}

instance towerK_vertexFixed (M : RationalQuiver.Rep Γ) (v : Γ.V) :
    IsScalarTower K ↥(stabField K L v) ↥(M.vertexFixed v) where
  smul_assoc c a x := by
    show ((c • a : ↥(stabField K L v))) • x = (algebraMap K ↥(stabField K L v) c) • (a • x)
    rw [Algebra.smul_def, mul_smul]

/-- Galois descent computes `W_v`'s dimension over `L(v)`: it is `dim_L M(v)`. -/
theorem finrank_vertexFixed (M : RationalQuiver.Rep Γ) (v : Γ.V)
    [FiniteDimensional L (M.M v)] :
    Module.finrank ↥(stabField K L v) ↥(M.vertexFixed v) = Module.finrank L (M.M v) := by
  rw [← (RationalQuiver.vertexDescentEquiv M v).finrank_eq,
    Module.finrank_baseChange (R := L) (S := ↥(stabField K L v))]

end Finrank

section NodeFinrank

set_option backward.isDefEq.respectTransparency.types false in
/-- The `ℚ`-dimension of `W_i` splits as `[L_i : ℚ] · dim_{ℚ[√-1]} M(v_i)`. -/
theorem finrank_W {Γ : RationalQuiver ℚ (Qi : Type)} (M : RationalQuiver.FDRep Γ)
    (i : Γ.toSpecies.I) :
    Module.finrank ℚ (((RationalQuiver.FFunctor Γ).obj M).W i)
      = Module.finrank ℚ ↥(stabField ℚ (Qi : Type) (Γ.vertexRep i))
        * Module.finrank (Qi : Type) (M.toRep.M (Γ.vertexRep i)) := by
  show Module.finrank ℚ ↥(M.toRep.vertexFixed (Γ.vertexRep i)) = _
  rw [← finrank_vertexFixed M.toRep (Γ.vertexRep i)]
  exact (Module.finrank_mul_finrank ℚ ↥(stabField ℚ (Qi : Type) (Γ.vertexRep i))
    ↥(M.toRep.vertexFixed (Γ.vertexRep i))).symm

theorem finrank_stabField_star : Module.finrank ℚ ↥(stabField ℚ (Qi : Type) (GQ.vertexRep starNode)) = 1 := by
  rw [stabField_star]
  exact IntermediateField.finrank_bot

theorem finrank_stabField_pm : Module.finrank ℚ ↥(stabField ℚ (Qi : Type) (GQ.vertexRep pmNode)) = 2 := by
  rw [stabField_pm, IntermediateField.finrank_top']
  exact Qi.finrank_eq_two

set_option backward.isDefEq.respectTransparency.types false in
theorem finrank_W_star (M : RationalQuiver.FDRep GQ) :
    Module.finrank ℚ (((RationalQuiver.FFunctor GQ).obj M).W starNode)
      = Module.finrank (Qi : Type) (M.toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 1)) := by
  rw [finrank_W, finrank_stabField_star, one_mul, vertexRep_starNode]

set_option backward.isDefEq.respectTransparency.types false in
theorem finrank_W_pm (M : RationalQuiver.FDRep GQ) :
    Module.finrank ℚ (((RationalQuiver.FFunctor GQ).obj M).W pmNode)
      = 2 * Module.finrank (Qi : Type) (M.toRep.M (GQ.vertexRep pmNode)) := by
  rw [finrank_W, finrank_stabField_pm]

end NodeFinrank
open scoped TensorProduct

section Vanishing

variable {K : Type} [Field K]

theorem mk_zero_left {A B Y X : Type} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [AddCommGroup Y] [Module K Y] [Module A Y] [Module Bᵐᵒᵖ Y] [IsScalarTower K A Y]
    [IsScalarTower K Bᵐᵒᵖ Y] [SMulCommClass A Bᵐᵒᵖ Y]
    [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X] [IsScalarTower K Aᵐᵒᵖ X] (y : Y) :
    Balanced.mk (K := K) (A := A) (B := B) (0 : X) y = 0 := by
  show Submodule.Quotient.mk (M := Y ⊗[K] X) (y ⊗ₜ[K] (0 : X)) = 0
  rw [TensorProduct.tmul_zero]
  rfl

theorem mk_zero_right {A B Y X : Type} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [AddCommGroup Y] [Module K Y] [Module A Y] [Module Bᵐᵒᵖ Y] [IsScalarTower K A Y]
    [IsScalarTower K Bᵐᵒᵖ Y] [SMulCommClass A Bᵐᵒᵖ Y]
    [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X] [IsScalarTower K Aᵐᵒᵖ X] (x : X) :
    Balanced.mk (K := K) (A := A) (B := B) x (0 : Y) = 0 := by
  show Submodule.Quotient.mk (M := Y ⊗[K] X) ((0 : Y) ⊗ₜ[K] x) = 0
  rw [TensorProduct.zero_tmul]
  rfl

variable {S : Species.{0} K} (V : Species.Rep S) (i j : S.I)

theorem f_zero_of_target (h : Subsingleton (V.W j)) : V.f i j = 0 :=
  LinearMap.ext fun _ => h.elim _ _

theorem f_zero_of_source (h : Subsingleton (V.W i)) : V.f i j = 0 := by
  refine Balanced.hom_ext fun x y => ?_
  rw [h.elim x 0, mk_zero_left]
  simp

theorem f_zero_of_edges (h : Subsingleton (S.M i j)) : V.f i j = 0 := by
  refine Balanced.hom_ext fun x y => ?_
  rw [h.elim y 0, mk_zero_right]
  simp

end Vanishing

/-- `E_{ii} = ∅`, so `{}_iM_i` is the empty product. -/
theorem M_diag_subsingleton (i : GQ.toSpecies.I) : Subsingleton (GQ.toSpecies.M i i) := by
  have hE : IsEmpty (GQ.edgeSet i i) :=
    RationalQuivers.Examples.gelfand_edgeSet_diag_isEmpty ℚ (Qi : Type) Qi.card_gal i
  have hQ : IsEmpty (GQ.EdgeOrbit i i) := ⟨fun q => hE.elim (Quotient.out q)⟩
  refine ⟨fun a b => ?_⟩
  show (a : ∀ ε : GQ.EdgeOrbit i i, ↥(GQ.edgeOrbitField ε)) = b
  exact funext fun ε => hQ.elim ε

theorem subsingleton_W_of_subsingleton (M : RationalQuiver.FDRep GQ) (i : GQ.toSpecies.I)
    (h : Subsingleton (M.toRep.M (GQ.vertexRep i))) :
    Subsingleton (((RationalQuiver.FFunctor GQ).obj M).W i) :=
  ⟨fun _ _ => Subtype.ext (h.elim _ _)⟩

/-! ### The descent formula, and the two consequences §6 needs -/

section Descent

open scoped Classical

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  {Γ : RationalQuiver K L}

open RationalQuiver

set_option backward.isDefEq.respectTransparency.types false in
/-- **The descent formula on a generator.**  `f_{ij}(w ⊗ m) = ∑_ε ∑_η (ητ_ε⁻¹)(m_ε)·Φ_{ε,η}(w)`,
read inside `M(v_j)`. -/
theorem edgeDescentOf_generator (M : Rep Γ) (i j : Γ.VertexOrbit)
    [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ ε))]
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) :
    ((edgeDescentOf M i j (Balanced.mk w m) : M.M (Γ.vertexRep j)))
      = ∑ ε : Γ.EdgeOrbit i j, ∑ η : EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ ε),
          ((EdgeChoice.rep Γ (EdgeChoice.choose Γ ε) η * (EdgeChoice.choose Γ ε).τ⁻¹)
              ((m ε : L))) • phiComp M (EdgeChoice.choose Γ ε) η w :=
  GelfandDescent.edgeDescentOf_generator M i j w m

/-- If every edge map of `M` vanishes, so does every descended structure map. -/
theorem edgeDescentOf_eq_zero_of_edges (M : Rep Γ) (i j : Γ.VertexOrbit)
    (hzero : ∀ e : Γ.E, M.φEdge e = 0) : edgeDescentOf M i j = 0 :=
  GelfandDescent.edgeDescentOf_eq_zero_of_edges M i j hzero

end Descent

/-! ### SP3: the cyclic (`ℓ = 0`) picture -/

noncomputable abbrev CQ : RationalQuiver ℚ (Qi : Type) := cyclicQ SqrtNegOneExt.qi.card_gal

/-- At `ℓ = k + 1` the headline functor `E_E ℚ ImagUnit.qi (k+1)` is T3's `E_EGel`, by definition.
@census none (helper) -/
theorem E_E_qi_succ (k : ℕ) :
    E_E ℚ ImagUnit.qi (k + 1) = Equivalence.E_EGel (D := ImagUnit.qi) (ℓ := k + 1) (by omega) := rfl

/-- **The native `𝔼_ℚ`** (`ℓ ≥ 1`): the headline functor `E_E ℚ ImagUnit.qi ℓ`, re-indexed along
`gelfandOfSign = gelfandOfCardTwo` to `Rep^nil(Γ_ℚ)` over `GQ`.  @census none (helper) -/
noncomputable abbrev EQNat {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    HC ℓ ℚ ImagUnit.qi ⥤ RepNilQ SqrtNegOneExt.qi.card_gal :=
  Equivalence.E_EGel (D := ImagUnit.qi) hℓ ⋙ (Compat.targetEquivCardTwo (D := ImagUnit.qi) Species.hcQ).functor

/-- **Engine ↔ native** (`ℓ ≥ 1`): the engine composite `EQFun` is the native `𝔼_ℚ`, componentwise the
identity (`Compat.engineNative`; `toHC ∘ toHCEObj = id` is `rfl`).  @census none (helper) -/
noncomputable def EQFun_iso_native {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : EQFun hℓ ≅ EQNat hℓ :=
  Functor.isoWhiskerLeft (Compat.toHCEObjFunctor (ℓ := ℓ) Species.hcQ)
    (Compat.engineNative (D := ImagUnit.qi) (ℓ := ℓ) Species.hcQ hℓ (Equivalence.E_Q_spec _ _))

/-- **`𝔼_ℚ(A)` for `ℓ ≥ 1`, as a representation of `Γ_ℚ`**, for the **native** `𝔼_ℚ = E_E ℚ ImagUnit.qi ℓ`
(re-indexed), with `Γ_ℚ` read over `ℚ[√-1] = Qi` (the type ascription is the point: instance search must
see `Qi`, not `SqrtNegOneExt.qi.carrier`).  The computations below unfold it to the engine's data by
`rfl` (identity components, `EQFun_iso_native`).  @census none (helper) -/
noncomputable abbrev EQObj {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (A : HC ℓ ℚ ImagUnit.qi) :
    RationalQuiver.FDRep GQ := ((EQNat hℓ).obj A).obj

/-- The native `𝔼_ℚ` at `ℓ = 0`, re-indexed to the cyclic quiver over `CQ`.  @census none (helper) -/
noncomputable abbrev ECycNat : HC 0 ℚ ImagUnit.qi ⥤ RepNilCycQ SqrtNegOneExt.qi.card_gal :=
  Cyclic.E_ECyc (D := ImagUnit.qi) ⋙ (Compat.targetEquivCardTwoZ (D := ImagUnit.qi) Species.hcQ).functor

/-- **Engine ↔ native** (`ℓ = 0`).  @census none (helper) -/
noncomputable def ECycFun_iso_native : ECycFun ≅ ECycNat :=
  Functor.isoWhiskerLeft (Compat.toHCEObjFunctor (ℓ := 0) Species.hcQ)
    (Compat.engineNativeZ (D := ImagUnit.qi) Species.hcQ (Cyclic.E_Cyc_spec _))

/-- **`𝔼_ℚ(A)` for `ℓ = 0`, as a representation of the cyclic quiver** (native).  @census none (helper) -/
noncomputable abbrev ECycObj (A : HC 0 ℚ ImagUnit.qi) : RationalQuiver.FDRep CQ :=
  (ECycNat.obj A).obj

theorem stabField_cyc (v : CQ.V) : stabField ℚ (Qi : Type) v = ⊤ :=
  stabField_eq_top_of_stabilizer_eq_bot
    (RationalQuivers.Examples.cyclic_stabilizer_V ℚ (Qi : Type) Qi.card_gal v)

theorem vertexRep_cycNode :
    CQ.vertexRep cycNode = vtxC SqrtNegOneExt.qi.card_gal 0 ∨ CQ.vertexRep cycNode = vtxC SqrtNegOneExt.qi.card_gal 1 := by
  have hc : ∀ v : Fin 2, v = 0 ∨ v = 1 := by decide
  exact hc (CQ.vertexRep cycNode)

/-! ### The two off-diagonal edge orbits of `Γ_ℚ` -/

theorem vertexClass_0 : GQ.vertexClass (vtxQ SqrtNegOneExt.qi.card_gal 0) = pmNode := rfl
theorem vertexClass_1 : GQ.vertexClass (vtxQ SqrtNegOneExt.qi.card_gal 1) = starNode := rfl
theorem vertexClass_2 : GQ.vertexClass (vtxQ SqrtNegOneExt.qi.card_gal 2) = pmNode :=
  RationalQuivers.Examples.gelfand_vertexClass_two ℚ (Qi : Type) Qi.card_gal

theorem fin4_cases : ∀ e : Fin 4, e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by decide

theorem edgeSet_star_pm (e : GQ.edgeSet starNode pmNode) :
    (e : GQ.E) = edgeQ SqrtNegOneExt.qi.card_gal 1 ∨ (e : GQ.E) = edgeQ SqrtNegOneExt.qi.card_gal 3 := by
  obtain ⟨e, hs, ht⟩ := e
  rcases fin4_cases e with rfl | rfl | rfl | rfl
  · exact absurd (by rw [← hs]; exact vertexClass_0) star_ne_pm
  · exact Or.inl rfl
  · exact absurd (by rw [← hs]; exact vertexClass_2) star_ne_pm
  · exact Or.inr rfl

theorem edgeSet_pm_star (e : GQ.edgeSet pmNode starNode) :
    (e : GQ.E) = edgeQ SqrtNegOneExt.qi.card_gal 0 ∨ (e : GQ.E) = edgeQ SqrtNegOneExt.qi.card_gal 2 := by
  obtain ⟨e, hs, ht⟩ := e
  rcases fin4_cases e with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd (by rw [← ht]; exact vertexClass_0) star_ne_pm
  · exact Or.inr rfl
  · exact absurd (by rw [← ht]; exact vertexClass_2) star_ne_pm

/-- The arrow `b₋ : ⋆ → −` as an element of `E_{{⋆},{±}}`. -/
noncomputable def eStarPm : GQ.edgeSet starNode pmNode := ⟨edgeQ SqrtNegOneExt.qi.card_gal 1, rfl, rfl⟩

/-- The arrow `a₋ : − → ⋆` as an element of `E_{{±},{⋆}}`. -/
noncomputable def ePmStar : GQ.edgeSet pmNode starNode := ⟨edgeQ SqrtNegOneExt.qi.card_gal 0, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem edgeOrbit_star_pm_subsingleton : Subsingleton (GQ.EdgeOrbit starNode pmNode) := by
  refine ⟨Quotient.ind fun a => Quotient.ind fun b => Quotient.sound ?_⟩
  have key : ∀ x y : GQ.edgeSet starNode pmNode,
      ((x : GQ.E) = edgeQ SqrtNegOneExt.qi.card_gal 1 ∨ (x : GQ.E) = edgeQ SqrtNegOneExt.qi.card_gal 3) →
      ((y : GQ.E) = edgeQ SqrtNegOneExt.qi.card_gal 1 ∨ (y : GQ.E) = edgeQ SqrtNegOneExt.qi.card_gal 3) →
      x ∈ MulAction.orbit Gal((Qi : Type)/ℚ) y := by
    intro x y hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact ⟨1, Subtype.ext (by rw [RationalQuiver.coe_smul_edgeSet, one_smul, hy, hx])⟩
    · exact ⟨galConj, Subtype.ext (by
        rw [RationalQuiver.coe_smul_edgeSet, hy, gelfandQ_smul_edge, hx]; rfl)⟩
    · exact ⟨galConj, Subtype.ext (by
        rw [RationalQuiver.coe_smul_edgeSet, hy, gelfandQ_smul_edge, hx]; rfl)⟩
    · exact ⟨1, Subtype.ext (by rw [RationalQuiver.coe_smul_edgeSet, one_smul, hy, hx])⟩
  exact key a b (edgeSet_star_pm a) (edgeSet_star_pm b)

set_option backward.isDefEq.respectTransparency.types false in
theorem edgeOrbit_pm_star_subsingleton : Subsingleton (GQ.EdgeOrbit pmNode starNode) := by
  refine ⟨Quotient.ind fun a => Quotient.ind fun b => Quotient.sound ?_⟩
  have key : ∀ x y : GQ.edgeSet pmNode starNode,
      ((x : GQ.E) = edgeQ SqrtNegOneExt.qi.card_gal 0 ∨ (x : GQ.E) = edgeQ SqrtNegOneExt.qi.card_gal 2) →
      ((y : GQ.E) = edgeQ SqrtNegOneExt.qi.card_gal 0 ∨ (y : GQ.E) = edgeQ SqrtNegOneExt.qi.card_gal 2) →
      x ∈ MulAction.orbit Gal((Qi : Type)/ℚ) y := by
    intro x y hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact ⟨1, Subtype.ext (by rw [RationalQuiver.coe_smul_edgeSet, one_smul, hy, hx])⟩
    · exact ⟨galConj, Subtype.ext (by
        rw [RationalQuiver.coe_smul_edgeSet, hy, gelfandQ_smul_edge, hx]; rfl)⟩
    · exact ⟨galConj, Subtype.ext (by
        rw [RationalQuiver.coe_smul_edgeSet, hy, gelfandQ_smul_edge, hx]; rfl)⟩
    · exact ⟨1, Subtype.ext (by rw [RationalQuiver.coe_smul_edgeSet, one_smul, hy, hx])⟩
  exact key a b (edgeSet_pm_star a) (edgeSet_pm_star b)

noncomputable instance : Unique (GQ.EdgeOrbit starNode pmNode) :=
  @Unique.mk' _ ⟨Quotient.mk _ eStarPm⟩ edgeOrbit_star_pm_subsingleton

noncomputable instance : Unique (GQ.EdgeOrbit pmNode starNode) :=
  @Unique.mk' _ ⟨Quotient.mk _ ePmStar⟩ edgeOrbit_pm_star_subsingleton

theorem stabilizer_pm : MulAction.stabilizer Gal((Qi : Type)/ℚ) (GQ.vertexRep pmNode) = ⊥ :=
  stabilizer_eq_bot_of_mem_orbit
    (MulAction.mem_orbit_symm.mp (GQ.mem_orbit_vertexRep (vtxQ SqrtNegOneExt.qi.card_gal 0)))
    (RationalQuivers.Examples.stabilizer_gelfandVertex_eq_bot ℚ (Qi : Type) Qi.card_gal 0
      (by decide))

theorem stabilizer_star : MulAction.stabilizer Gal((Qi : Type)/ℚ) (GQ.vertexRep starNode) = ⊤ :=
  stabilizer_eq_top_of_mem_orbit
    (MulAction.mem_orbit_symm.mp (GQ.mem_orbit_vertexRep (vtxQ SqrtNegOneExt.qi.card_gal 1)))
    (RationalQuivers.Examples.stabilizer_gelfandVertex_star ℚ (Qi : Type) Qi.card_gal)

section DescentTools

open scoped Classical

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  {Γ : RationalQuiver K L}

open RationalQuiver

/-- If every edge **from `i` to `j`** vanishes, so does `f_{ij}`. -/
theorem edgeDescentOf_eq_zero_of_edgeSet (M : Rep Γ) (i j : Γ.VertexOrbit)
    (hzero : ∀ e : Γ.edgeSet i j, M.φEdge (e : Γ.E) = 0) : edgeDescentOf M i j = 0 :=
  GelfandDescent.edgeDescentOf_eq_zero_of_edgeSet M i j hzero

/-- When the target vertex has trivial stabilizer, the coset system is a point. -/
theorem rep_eq_one {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε)
    (h : MulAction.stabilizer Gal(L/K) (Γ.vertexRep j) = ⊥)
    (η : EdgeChoice.CosetIndex Γ ch) : EdgeChoice.rep Γ ch η = 1 :=
  GelfandDescent.rep_eq_one ch h η

theorem cosetIndex_subsingleton {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε)
    (h : MulAction.stabilizer Gal(L/K) (Γ.vertexRep j) = ⊥) :
    Subsingleton (EdgeChoice.CosetIndex Γ ch) :=
  GelfandDescent.cosetIndex_subsingleton ch h

end DescentTools

section Generation

variable {K : Type} [Field K]

/-- If `X` is generated over `A` by `x₀`, every element of `X ⊗_A Y` is `x₀ ⊗ y`. -/
theorem balanced_eq_mk {A B Y X : Type} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [AddCommGroup Y] [Module K Y] [Module A Y] [Module Bᵐᵒᵖ Y] [IsScalarTower K A Y]
    [IsScalarTower K Bᵐᵒᵖ Y] [SMulCommClass A Bᵐᵒᵖ Y]
    [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X] [IsScalarTower K Aᵐᵒᵖ X]
    (x₀ : X) (hX : ∀ x : X, ∃ a : A, MulOpposite.op a • x₀ = x)
    (t : Balanced K A B Y X) : ∃ y : Y, t = Balanced.mk x₀ y := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K A B Y X) t
  induction s with
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

end Generation

section UniqueOrbit

open scoped Classical

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  {Γ : RationalQuiver K L}

open RationalQuiver

set_option backward.isDefEq.respectTransparency.types false in
/-- The descent formula when there is exactly one edge orbit from `i` to `j`. -/
theorem edgeDescentOf_uniqueOrbit (M : Rep Γ) (i j : Γ.VertexOrbit)
    [Unique (Γ.EdgeOrbit i j)] [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ ε))]
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) :
    ((edgeDescentOf M i j (Balanced.mk w m) : M.M (Γ.vertexRep j)))
      = ∑ η : EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)),
          ((EdgeChoice.rep Γ (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)) η
              * (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)).τ⁻¹)
            ((m default : L))) • phiComp M (EdgeChoice.choose Γ default) η w :=
  GelfandDescent.edgeDescentOf_uniqueOrbit M i j w m

end UniqueOrbit

section PhiComp

open scoped Classical

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  {Γ : RationalQuiver K L}

open RationalQuiver

theorem phiComp_eq (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch)
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) :
    phiComp M ch η w
      = M.φ' (EdgeChoice.rep Γ ch η * ch.τ⁻¹) (ch.cosetTarget η)
        (M.φEdge (Γ.edgeRep ε) (M.φ' ch.σ ch.sourceVertex (w : M.M (Γ.vertexRep i)))) :=
  GelfandDescent.phiComp_eq M ch η w

/-- `Φ_{ε,η}` is injective as soon as the edge map is: the two other factors are bijections. -/
theorem phiComp_ne_zero (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch)
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) (hw : (w : M.M (Γ.vertexRep i)) ≠ 0)
    (hinj : Function.Injective (M.φEdge (Γ.edgeRep ε))) : phiComp M ch η w ≠ 0 :=
  GelfandDescent.phiComp_ne_zero M ch η w hw hinj

end PhiComp

theorem exists_smul_eq_of_finrank_one {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (h : Module.finrank F V = 1) {v₀ : V} (hv : v₀ ≠ 0) (v : V) : ∃ c : F, c • v₀ = v :=
  (finrank_eq_one_iff_of_nonzero' v₀ hv).mp h v

theorem exists_ne_zero_of_finrank_one {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (h : Module.finrank F V = 1) : ∃ v : V, v ≠ 0 := by
  haveI : Nontrivial V := by
    refine Module.nontrivial_of_finrank_pos (R := F) ?_
    rw [h]; norm_num
  exact exists_ne 0

/-! ### The two structure maps of `Γ_ℚ`'s species, at a general `M` -/

section Concrete

open scoped Classical

open RationalQuiver MulAction

noncomputable instance cosetGQ_fintype (i j : GQ.VertexOrbit) :
    ∀ ε : GQ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex GQ (EdgeChoice.choose GQ ε)) :=
  fun ε => @Fintype.ofFinite _ (finite_cosetIndex (EdgeChoice.choose GQ ε))

noncomputable instance edgeOrbitGQ_fintype (i j : GQ.VertexOrbit) :
    Fintype (GQ.EdgeOrbit i j) := Fintype.ofFinite _

theorem edgeOrbitField_top {i j : GQ.VertexOrbit} (ε : GQ.EdgeOrbit i j) :
    GQ.edgeOrbitField ε = ⊤ :=
  RationalQuivers.Examples.gelfand_edgeOrbitField ℚ (Qi : Type) Qi.card_gal ε

/-- `Φ_{ε,η}` split as `φ_{rep η} ∘ φ_{τ⁻¹} ∘ φ_e ∘ φ_σ`. -/
theorem phiComp_split {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {Γ : RationalQuiver K L} (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch)
    (w : ↥(M.vertexFixed (Γ.vertexRep i)))
    (hst : EdgeChoice.rep Γ ch η • Γ.vertexRep j = Γ.vertexRep j) :
    phiComp M ch η w
      = M.φ' (EdgeChoice.rep Γ ch η) hst
          (M.φ' ch.τ⁻¹ ch.inv_smul_target
            (M.φEdge (Γ.edgeRep ε) (M.φ' ch.σ ch.sourceVertex (w : M.M (Γ.vertexRep i))))) :=
  GelfandDescent.phiComp_split M ch η w hst

/-- The underlying vector of an element of `W_i`. -/
def wv (M : RationalQuiver.FDRep GQ) (i : GQ.toSpecies.I)
    (w : ((RationalQuiver.FFunctor GQ).obj M).W i) : M.toRep.M (GQ.vertexRep i) :=
  (show ↥(M.toRep.vertexFixed (GQ.vertexRep i)) from w).val

theorem wv_inj (M : RationalQuiver.FDRep GQ) (i : GQ.toSpecies.I)
    {a b : ((RationalQuiver.FFunctor GQ).obj M).W i} (h : wv M i a = wv M i b) : a = b :=
  Subtype.ext h

set_option backward.isDefEq.respectTransparency.types false in
theorem wv_zero (M : RationalQuiver.FDRep GQ) (i : GQ.toSpecies.I) :
    wv M i (0 : ((RationalQuiver.FFunctor GQ).obj M).W i) = 0 := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The balanced product `W_i ⊗_{L_i} {}_iM_j`. -/
noncomputable abbrev Ten (M : RationalQuiver.FDRep GQ) (i j : GQ.toSpecies.I) : Type :=
  GQ.toSpecies.toSpecies.RepTensor i j (((RationalQuiver.FFunctor GQ).obj M).W i)

set_option backward.isDefEq.respectTransparency.types false in
/-- The generator `w ⊗ m`. -/
noncomputable abbrev tmk (M : RationalQuiver.FDRep GQ) (i j : GQ.toSpecies.I)
    (w : ((RationalQuiver.FFunctor GQ).obj M).W i) (m : GQ.toSpecies.toSpecies.M i j) :
    Ten M i j := Balanced.mk w m

set_option backward.isDefEq.respectTransparency.types false in
theorem tmk_zero_right (M : RationalQuiver.FDRep GQ) (i j : GQ.toSpecies.I)
    (w : ((RationalQuiver.FFunctor GQ).obj M).W i) : tmk M i j w 0 = 0 :=
  mk_zero_right w

set_option backward.isDefEq.respectTransparency.types false in
theorem exists_tmk (M : RationalQuiver.FDRep GQ) (i j : GQ.toSpecies.I)
    (x₀ : ((RationalQuiver.FFunctor GQ).obj M).W i)
    (hX : ∀ x : ((RationalQuiver.FFunctor GQ).obj M).W i,
      ∃ a : GQ.toSpecies.toSpecies.L i, MulOpposite.op a • x₀ = x)
    (t : Ten M i j) : ∃ m : GQ.toSpecies.toSpecies.M i j, t = tmk M i j x₀ m :=
  balanced_eq_mk x₀ hX t

/-! #### The `{⋆} → {±}` map -/

noncomputable abbrev chSP : GQ.EdgeChoice (default : GQ.EdgeOrbit starNode pmNode) :=
  EdgeChoice.choose GQ default

set_option backward.isDefEq.respectTransparency.types false in
theorem f_star_pm_generator (M : RationalQuiver.FDRep GQ)
    (w : ((RationalQuiver.FFunctor GQ).obj M).W starNode)
    (m : GQ.toSpecies.toSpecies.M starNode pmNode)
    (η₀ : EdgeChoice.CosetIndex GQ chSP) :
    wv M pmNode (((RationalQuiver.FFunctor GQ).obj M).f starNode pmNode (tmk M starNode pmNode w m))
      = chSP.τ⁻¹ ((m default : (Qi : Type))) • phiComp M.toRep chSP η₀ w :=
  GelfandDescent.f_uniqueOrbit_generator M starNode pmNode stabilizer_pm w m η₀

set_option backward.isDefEq.respectTransparency.types false in
/-- `f_{{⋆},{±}}` is bijective as soon as the two `K`-type spaces are lines and the arrows
`⋆ → ±` are injective. -/
theorem species_star_pm_bijective (M : RationalQuiver.FDRep GQ)
    (hstar : Module.finrank (Qi : Type) (M.toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 1)) = 1)
    (hpm : Module.finrank (Qi : Type) (M.toRep.M (GQ.vertexRep pmNode)) = 1)
    (hinj : ∀ e : GQ.edgeSet starNode pmNode,
      Function.Injective (M.toRep.φEdge (e : GQ.E))) :
    Function.Bijective (((RationalQuiver.FFunctor GQ).obj M).f starNode pmNode) := by
  have hW1 : Module.finrank ↥(stabField ℚ (Qi : Type) (GQ.vertexRep starNode))
      ↥(M.toRep.vertexFixed (GQ.vertexRep starNode)) = 1 := by
    rw [finrank_vertexFixed, vertexRep_starNode]; exact hstar
  have hW1' : Module.finrank (GQ.toSpecies.L starNode)
      (((RationalQuiver.FFunctor GQ).obj M).W starNode) = 1 := hW1
  obtain ⟨x₀, hx₀⟩ := exists_ne_zero_of_finrank_one hW1'
  have hx₀' : wv M starNode x₀ ≠ 0 :=
    fun h => hx₀ (wv_inj M starNode (h.trans (wv_zero M starNode).symm))
  have hgen : ∀ x : ((RationalQuiver.FFunctor GQ).obj M).W starNode,
      ∃ a : GQ.toSpecies.toSpecies.L starNode, MulOpposite.op a • x₀ = x :=
    exists_smul_eq_of_finrank_one hW1' hx₀
  haveI hsub := cosetIndex_subsingleton chSP stabilizer_pm
  obtain ⟨η₀⟩ : Nonempty (EdgeChoice.CosetIndex GQ chSP) := ⟨QuotientGroup.mk 1⟩
  have hinj' : Function.Injective
      (M.toRep.φEdge (GQ.edgeRep (default : GQ.EdgeOrbit starNode pmNode))) :=
    hinj (Quotient.out default)
  have hu : phiComp M.toRep chSP η₀ x₀ ≠ 0 :=
    phiComp_ne_zero M.toRep _ η₀ x₀ hx₀' hinj'
  constructor
  · refine (injective_iff_map_eq_zero _).mpr fun t ht => ?_
    obtain ⟨y, rfl⟩ := exists_tmk M starNode pmNode x₀ hgen t
    have hval := f_star_pm_generator M x₀ y η₀
    rw [ht, wv_zero] at hval
    have hzero : chSP.τ⁻¹ ((y default : (Qi : Type))) = 0 :=
      (smul_eq_zero.mp hval.symm).resolve_right hu
    have hy : y default = 0 := by
      refine Subtype.ext ?_
      exact (EmbeddingLike.apply_eq_iff_eq chSP.τ⁻¹).mp (hzero.trans (map_zero _).symm)
    have hy0 : y = 0 := by
      funext e
      have he : e = default := Unique.eq_default e
      subst he
      exact hy
    rw [hy0]
    exact tmk_zero_right M starNode pmNode x₀
  · intro w
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_one hpm hu (wv M pmNode w)
    refine ⟨tmk M starNode pmNode x₀
      (fun e => ⟨chSP.τ c, by rw [edgeOrbitField_top]; trivial⟩), ?_⟩
    refine wv_inj M pmNode ?_
    rw [f_star_pm_generator M x₀ _ η₀]
    rw [show chSP.τ⁻¹ ((⟨chSP.τ c, by rw [edgeOrbitField_top]; trivial⟩ :
        ↥(GQ.edgeOrbitField (default : GQ.EdgeOrbit starNode pmNode))) : (Qi : Type)) = c from
      AlgEquiv.symm_apply_apply chSP.τ c]
    exact hc

/-! #### The `{±} → {⋆}` map -/

noncomputable abbrev chPS : GQ.EdgeChoice (default : GQ.EdgeOrbit pmNode starNode) :=
  EdgeChoice.choose GQ default

theorem stab_all (σ : Gal((Qi : Type)/ℚ)) :
    σ • GQ.vertexRep starNode = GQ.vertexRep starNode :=
  GelfandDescent.stab_all_of_stab_top stabilizer_star σ

theorem gal_univ : (Finset.univ : Finset Gal((Qi : Type)/ℚ)) = {1, galConj} :=
  GelfandDescent.gal_univ_of_card_two Qi.card_gal galConj_ne_one

/-- `η ↦ rep η` is a bijection from the coset system at `⋆` onto the Galois group. -/
theorem rep_bijective_star {ε : GQ.EdgeOrbit pmNode starNode} (ch : GQ.EdgeChoice ε) :
    Function.Bijective (fun η : EdgeChoice.CosetIndex GQ ch => EdgeChoice.rep GQ ch η) :=
  GelfandDescent.rep_bijective_of_stab_top ch stabilizer_star
    (fun e => RationalQuivers.Examples.gelfand_stabilizer_E ℚ (Qi : Type) Qi.card_gal e)

/-- The vector `φ_{τ⁻¹} φ_e φ_σ (w)` in `M(v_⋆)` that the `{±} → {⋆}` map traces. -/
noncomputable def uPS (M : RationalQuiver.FDRep GQ)
    (w : ((RationalQuiver.FFunctor GQ).obj M).W pmNode) : M.toRep.M (GQ.vertexRep starNode) :=
  GelfandDescent.uPS M pmNode starNode w

theorem uPS_def (M : RationalQuiver.FDRep GQ)
    (w : ((RationalQuiver.FFunctor GQ).obj M).W pmNode) :
    uPS M w = M.toRep.φ' chPS.τ⁻¹ chPS.inv_smul_target
      (M.toRep.φEdge (GQ.edgeRep (default : GQ.EdgeOrbit pmNode starNode))
        (M.toRep.φ' chPS.σ chPS.sourceVertex (wv M pmNode w))) :=
  GelfandDescent.uPS_def M pmNode starNode w

set_option backward.isDefEq.respectTransparency.types false in
theorem f_pm_star_generator (M : RationalQuiver.FDRep GQ)
    (w : ((RationalQuiver.FFunctor GQ).obj M).W pmNode)
    (m : GQ.toSpecies.toSpecies.M pmNode starNode) :
    wv M starNode (((RationalQuiver.FFunctor GQ).obj M).f pmNode starNode (tmk M pmNode starNode w m))
      = chPS.τ⁻¹ ((m default : (Qi : Type))) • uPS M w
        + galConj (chPS.τ⁻¹ ((m default : (Qi : Type))))
          • M.toRep.φ' galConj (stab_all galConj) (uPS M w) :=
  GelfandDescent.f_twoTerm_generator M pmNode starNode stabilizer_star
    (fun e => RationalQuivers.Examples.gelfand_stabilizer_E ℚ (Qi : Type) Qi.card_gal e)
    Qi.card_gal galConj_ne_one w m

set_option backward.isDefEq.respectTransparency.types false in
/-- `f_{{±},{⋆}}` is surjective as soon as the `K`-type spaces are lines and the arrows
`± → ⋆` are injective. -/
theorem species_pm_star_surjective (M : RationalQuiver.FDRep GQ)
    (hstar : Module.finrank (Qi : Type) (M.toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 1)) = 1)
    (hpm : Module.finrank (Qi : Type) (M.toRep.M (GQ.vertexRep pmNode)) = 1)
    (hinj : ∀ e : GQ.edgeSet pmNode starNode,
      Function.Injective (M.toRep.φEdge (e : GQ.E))) :
    Function.Surjective (((RationalQuiver.FFunctor GQ).obj M).f pmNode starNode) := by
  have hWpm : Module.finrank ↥(stabField ℚ (Qi : Type) (GQ.vertexRep pmNode))
      ↥(M.toRep.vertexFixed (GQ.vertexRep pmNode)) = 1 := by
    rw [finrank_vertexFixed]; exact hpm
  have hWst : Module.finrank ↥(stabField ℚ (Qi : Type) (GQ.vertexRep starNode))
      ↥(M.toRep.vertexFixed (GQ.vertexRep starNode)) = 1 := by
    rw [finrank_vertexFixed, vertexRep_starNode]; exact hstar
  have hWpm' : Module.finrank (GQ.toSpecies.L pmNode)
      (((RationalQuiver.FFunctor GQ).obj M).W pmNode) = 1 := hWpm
  obtain ⟨x₀, hx₀⟩ := exists_ne_zero_of_finrank_one hWpm' 
  have hx₀' : wv M pmNode x₀ ≠ 0 :=
    fun h => hx₀ (wv_inj M pmNode (h.trans (wv_zero M pmNode).symm))
  have hinj' : Function.Injective
      (M.toRep.φEdge (GQ.edgeRep (default : GQ.EdgeOrbit pmNode starNode))) :=
    hinj (Quotient.out default)
  have hu : uPS M x₀ ≠ 0 := by
    intro h
    rw [uPS_def] at h
    have h1 := (AddEquiv.map_eq_zero_iff (M.toRep.φ' chPS.τ⁻¹ chPS.inv_smul_target)).mp h
    have h2 : M.toRep.φ' chPS.σ chPS.sourceVertex (wv M pmNode x₀) = 0 :=
      hinj' (by rw [h1, map_zero])
    exact hx₀' ((AddEquiv.map_eq_zero_iff (M.toRep.φ' chPS.σ chPS.sourceVertex)).mp h2)
  obtain ⟨z, hz⟩ : ∃ z : (Qi : Type),
      z • uPS M x₀ + galConj z • M.toRep.φ' galConj (stab_all galConj) (uPS M x₀) ≠ 0 := by
    by_cases h1 : uPS M x₀ + M.toRep.φ' galConj (stab_all galConj) (uPS M x₀) = 0
    · obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp galConj_ne_one
      have hzz : galConj z ≠ z := hz
      have hneg : M.toRep.φ' galConj (stab_all galConj) (uPS M x₀) = -(uPS M x₀) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact h1
      refine ⟨z, ?_⟩
      rw [hneg, smul_neg, ← sub_eq_add_neg, ← sub_smul]
      intro hcon
      rcases smul_eq_zero.mp hcon with h | h
      · exact hzz (sub_eq_zero.mp h).symm
      · exact hu h
    · exact ⟨1, by rw [one_smul, map_one, one_smul]; exact h1⟩
  have hzval : chPS.τ⁻¹ ((⟨chPS.τ z, by rw [edgeOrbitField_top]; trivial⟩ :
      ↥(GQ.edgeOrbitField (default : GQ.EdgeOrbit pmNode starNode))) : (Qi : Type)) = z :=
    AlgEquiv.symm_apply_apply chPS.τ z
  have hne : ((RationalQuiver.FFunctor GQ).obj M).f pmNode starNode
      (tmk M pmNode starNode x₀ (fun e => ⟨chPS.τ z, by rw [edgeOrbitField_top]; trivial⟩))
        ≠ 0 := by
    intro h
    apply hz
    rw [← hzval, ← f_pm_star_generator M x₀
      (fun e => ⟨chPS.τ z, by rw [edgeOrbitField_top]; trivial⟩), h, wv_zero]
  intro w
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_one hWst hne w
  exact ⟨MulOpposite.op (show GQ.toSpecies.toSpecies.L starNode from a) • tmk M pmNode starNode x₀
    (fun e => ⟨chPS.τ z, by rw [edgeOrbitField_top]; trivial⟩), (map_smul _ _ _).trans ha⟩

end Concrete

/-! ### SP4 / SP5 -/

end SpeciesG4

end RationalQuivers.Examples
