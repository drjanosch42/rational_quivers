import Mathlib.LinearAlgebra.TensorProduct.Tower
import RationalQuivers.HC.Category
import RationalQuivers.Unipotent.Nilpotent

/-!
# `§3.3` Rational normalizations over every field (`prop:XY_C_relation` … `def:xstarystar`)

The opening of tex §5.1
records that these statements hold for an **arbitrary** weight module `M_{L_E}` in
`HC_λ(𝔤,K)_{L_E}`, not only for a base change: their proofs use only `C = H² − 2H + 4XY + 1`.
They are therefore stated for any `W : WeightData F M` over a field `F` (of characteristic `0`
where `γ_⋆ = (ℓ-1)!` must be invertible), with the generalized infinitesimal character as a
hypothesis; the `G_E`-clauses ("if `√-1 ∉ E`, `n̄` is the complex conjugate of `n`") are stated on
`A : HC ℓ E D` for **every** `σ ∈ G_E` (trivial when `G_E = 1`).

## Contents

* `casimirFactorProd`, `nilpScalar`, `prop:XY_C_relation` (`pow_X_pow_Y_eq_prod_casimir`,
  `pow_Y_pow_X_eq_prod_casimir`) and its nilpotent refinement (`pow_X_pow_Y_eq_scalar_add_nilpotent`,
  `pow_Y_pow_X_eq_scalar_add_nilpotent`) — `prop:XY_C_relation` and `prop:xyscalarplusnilpotent`,
  field-generic.
* the combinatorial identity `∏ (ℓ² − (ℓ−2−2j)²) = 4^{ℓ−1}((ℓ−1)!)²` and the component lemmas.
* `WeightData.isUnit_pow_X`, `WeightData.Tplus`/`Tminus`/`Tplus_isUnit`, `WeightData.xStar`/`yStar`
  and `WeightData.xStar_yStar_relations` — `cor:X_Y_inverses`, `cor:T_operators`, `def:xstarystar`
  over any field `F` of characteristic `0`.
* `HC.galAct_normRemainder_of_chi_neg_one` (the source's argument), `HC.galAct_normRemainder`,
  `HC.galAct_nStar` — the `G_E`-clauses on `A : HC ℓ E D`.

All new declarations live in the namespaces `RationalQuivers.HC.WeightData` and
`RationalQuivers.HC.HC`, so that dot notation (`W.isUnit_pow_X`, `A.galAct_normRemainder`) reaches
them and their short names did not collide with the `ℚ`-bound statements on `HC.RationalSetup`,
which were in the tree when this module was written.  *(2026-10-21, O-V2-6 round 2: v2 WP-8,
`d2a2a47`, moved `HC.RationalSetup` and those statements to `Gelfand/QNormalization.lean`, and
WP-13 deleted that module, `9c6b193`.)*
-/

universe u v

namespace RationalQuivers.HC

open scoped TensorProduct

section Prod

variable {E : Type u} [Field E] {M : Type v} [AddCommGroup M] [Module E M]

/-- `∏_{j=0}^{m-1} (A - (k - 2j)² · 1)`, the right-hand side of `eq:XYm_via_C` / `eq:YXm_via_C`,
in ascending `j`.  The factors pairwise commute, so the order is immaterial; fixing one keeps the
statement a single term (module docstring).

@census none
-/
def casimirFactorProd (A : Module.End E M) (k : ℤ) (m : ℕ) : Module.End E M :=
  ((List.range m).map fun j =>
    A - (((k - 2 * (j : ℤ) : ℤ) : E) ^ 2) • (1 : Module.End E M)).prod

/-- `∏_{j=0}^{m-1} (ℓ² - (k - 2j)²)`, the explicit scalar of `eq:XYm_nilp`
(clause `RQ2-3.05-C5`).

@census none
-/
def nilpScalar (ℓ : ℕ) (k : ℤ) (m : ℕ) (E : Type u) [Field E] : E :=
  ((List.range m).map fun j => ((ℓ : E) ^ 2 - (((k - 2 * (j : ℤ) : ℤ) : E) ^ 2))).prod

/-! ### The two products, their recursions, and the centrality they inherit from `C` -/

/-- The coercion `List ℕ → List ℤ` that `casimirFactorProd` and `nilpScalar` elaborate to, written
as a `List.map` so that `List.range_succ_eq_map` can be applied through it.

@census none
-/
theorem list_coe_eq_map (l : List ℕ) : ((l : List ℕ) : List ℤ) = l.map (fun j : ℕ => (j : ℤ)) := by
  induction l with
  | nil => rfl
  | cons a t ih => simpa using ih

/-- The empty product is `1`.

@census none
-/
theorem casimirFactorProd_zero (A : Module.End E M) (k : ℤ) : casimirFactorProd A k 0 = 1 := rfl

/-- **The recursion the induction of `prop:XY_C_relation` runs on**: peeling `j = 0` off
`∏_{j<m+1}(A - (k-2j)²)` leaves the factor `A - k²` times the *same* product at `k-2`.

@census none
-/
theorem casimirFactorProd_succ (A : Module.End E M) (k : ℤ) (m : ℕ) :
    casimirFactorProd A k (m + 1)
      = (A - (((k : ℤ) : E) ^ 2) • (1 : Module.End E M)) * casimirFactorProd A (k - 2) m := by
  unfold casimirFactorProd
  rw [list_coe_eq_map, list_coe_eq_map, List.range_succ_eq_map]
  simp only [List.map_map, List.map_cons, List.prod_cons]
  congr 1
  · norm_num
  · apply congrArg List.prod
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply]
    congr 3
    push_cast
    ring

/-- The empty scalar product is `1`.

@census none
-/
theorem nilpScalar_zero (ℓ : ℕ) (k : ℤ) : nilpScalar ℓ k 0 E = 1 := rfl

/-- The scalar recursion matching `casimirFactorProd_succ`.

@census none
-/
theorem nilpScalar_succ (ℓ : ℕ) (k : ℤ) (m : ℕ) :
    nilpScalar ℓ k (m + 1) E = ((ℓ : E) ^ 2 - ((k : ℤ) : E) ^ 2) * nilpScalar ℓ (k - 2) m E := by
  unfold nilpScalar
  rw [list_coe_eq_map, list_coe_eq_map, List.range_succ_eq_map]
  simp only [List.map_map, List.map_cons, List.prod_cons]
  congr 1
  · norm_num
  · apply congrArg List.prod
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply]
    congr 2
    push_cast
    ring

/-- Every factor of `casimirFactorProd A k m` is a polynomial in `A`, so the product commutes with
anything `A` commutes with.

@census none
-/
theorem commute_casimirFactorProd (A B : Module.End E M) (h : Commute A B) (k : ℤ) (m : ℕ) :
    Commute (casimirFactorProd A k m) B := by
  induction m generalizing k with
  | zero => rw [casimirFactorProd_zero]; exact Commute.one_left B
  | succ m ih =>
    rw [casimirFactorProd_succ]
    exact Commute.mul_left (h.sub_left ((Commute.one_left B).smul_left _)) (ih (k - 2))

/-- The product commutes with every factor `C - c·1`, which is what lets the induction step
re-order the peeled factor.

@census none
-/
theorem casimir_commute_factorProd (W : WeightData E M) (k : ℤ) (m : ℕ) (c : E) :
    Commute (casimirFactorProd W.casimir k m) (W.casimir - c • (1 : Module.End E M)) :=
  commute_casimirFactorProd _ _
    ((Commute.refl W.casimir).sub_right ((Commute.one_right W.casimir).smul_right c)) k m

/-! ### The explicit remainder of `prop:xyscalarplusnilpotent`

`RQ2-3.05` asks only for *some* nilpotent remainder, but `RQ2-3.06`'s clause `C6` needs the two
remainders of `eq:XY_inverses_rel` to be Galois-conjugate to each other, which an arbitrary
existential witness cannot supply.  The remainder is therefore **named**:
`casimirFactorProd C k m - nilpScalar ℓ k m · 1`, a polynomial in the Casimir, the *same*
operator on both sides.  It is nilpotent because it is `(C - ℓ²·1) · p` for a `p` commuting with
`C - ℓ²·1`, which is what `exists_casimirRemainder` establishes.
-/

/-- `∏_{j<m}(C - (k-2j)²) = (∏_{j<m}(ℓ² - (k-2j)²))·1 + (C - ℓ²·1)·p` with `p` commuting with
`C - ℓ²·1`: expand each factor as `(C - ℓ²·1) + (ℓ² - (k-2j)²)·1`.

@census none
-/
theorem exists_casimirRemainder (W : WeightData E M) (ℓ : ℕ) (k : ℤ) (m : ℕ) :
    ∃ p : Module.End E M,
      Commute (W.casimir - ((ℓ : E) ^ 2) • (1 : Module.End E M)) p ∧
      casimirFactorProd W.casimir k m
        = (nilpScalar ℓ k m E) • (1 : Module.End E M)
          + (W.casimir - ((ℓ : E) ^ 2) • (1 : Module.End E M)) * p := by
  induction m generalizing k with
  | zero =>
    exact ⟨0, Commute.zero_right _, by rw [casimirFactorProd_zero, nilpScalar_zero]; simp⟩
  | succ m ih =>
    obtain ⟨p, hcp, hp⟩ := ih (k - 2)
    set N := W.casimir - ((ℓ : E) ^ 2) • (1 : Module.End E M) with hN
    set a : E := (ℓ : E) ^ 2 - (((k : ℤ) : E)) ^ 2 with ha
    set s : E := nilpScalar ℓ (k - 2) m E with hs
    refine ⟨s • (1 : Module.End E M) + N * p + a • p, ?_, ?_⟩
    · exact (((Commute.one_right N).smul_right s).add_right
        ((Commute.refl N).mul_right hcp)).add_right (hcp.smul_right a)
    · have hCk : W.casimir - ((((k : ℤ) : E)) ^ 2) • (1 : Module.End E M) = N + a • 1 := by
        rw [hN, ha, sub_smul]
        abel
      rw [casimirFactorProd_succ, nilpScalar_succ, hp, hCk, ← ha, ← hs]
      simp only [add_mul, mul_add, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, smul_add,
        smul_smul]
      module

/-- **The named remainder of `prop:xyscalarplusnilpotent` is nilpotent**, when `C - ℓ²·1` is.

@census none
-/
theorem isNilpotent_casimirRemainder (W : WeightData E M) (ℓ : ℕ) (k : ℤ) (m : ℕ)
    (hnil : IsNilpotent (W.casimir - ((ℓ : E) ^ 2) • (1 : Module.End E M))) :
    IsNilpotent (casimirFactorProd W.casimir k m
      - (nilpScalar ℓ k m E) • (1 : Module.End E M)) := by
  obtain ⟨p, hcp, hp⟩ := exists_casimirRemainder W ℓ k m
  rw [hp, add_sub_cancel_left]
  exact hcp.isNilpotent_mul_right hnil

/-! ## §3.3 — `prop:XY_C_relation` and its nilpotent refinement -/

/-- **Proposition** (`prop:XY_C_relation`, census `RQ2-3.04`).  For **every** `m ≥ 0` and **every**
`k ∈ ℤ`,
`4^m X^m Y^m : M_{k+1} → M_{k+1}` equals `∏_{j=0}^{m-1} (C|_{M_{k+1}} - (k-2j)² · 1)`
(`eq:XYm_via_C`).  The restriction to `M_{k+1}` is rendered as "for every `v ∈ M_{k+1}`", which is
what "as a map `M_{k+1} → M_{k+1}`" says; both sides do preserve `M_{k+1}` by `X_mem`/`Y_mem`.

The companion identity `eq:YXm_via_C` (clause `RQ2-3.04-C2`) is `pow_Y_pow_X_eq_prod_casimir`; the
census records it as a separate conclusion, not a corollary.

@census    RQ2-3.04
@source    prop:XY_C_relation
@clauses   RQ2-3.04-H1, RQ2-3.04-H2, RQ2-3.04-C1,
           RQ2-5.12-S-O3
@imports   none
@divergence JUSTIFIED_REFORMULATION (arbitrary weight module over an arbitrary field, disclosed).
Clause `RQ2-3.04-H2` is §3.3's standing setup: `M_E ∈ HC_λ(𝔤,K)_E` over a field `E` of
characteristic `0`, `M_{L_E} := L_E ⊗_E M_E` and `M_n := M_{L_E}[χ_n]`.  This statement is proved
for an arbitrary field `E` and an arbitrary `WeightData E M`, of which that setup is one instance
(`HC.weight`, the weight data of `M_{L_E}` over `L_E`), and which the opening of tex §5.1 permits
("also valid for an arbitrary `M_{L_E} ∈ HC_λ(𝔤,K)_{L_E}`").  Nothing in the identity uses the
base field or the base-change origin of `M`: the source's proof uses only `4XY = C - p²` on
`M_{p+1}` and `[C,X] = [C,Y] = 0`, i.e. only the relations recorded in `WeightData`.  The
generalisation is strictly stronger than the source's statement; the standing clause is cited.
-/
theorem pow_X_pow_Y_eq_prod_casimir (W : WeightData E M) (m : ℕ) (k : ℤ) (v : M)
    (hv : v ∈ W.comp (k + 1)) :
    ((4 : E) ^ m • (W.X ^ m * W.Y ^ m)) v = casimirFactorProd W.casimir k m v := by
  induction m generalizing k v with
  | zero => simp [casimirFactorProd_zero]
  | succ m ih =>
    have hYv : W.Y v ∈ W.comp ((k - 2) + 1) := by
      have h := W.Y_mem _ _ hv
      have he : k + 1 - 2 = k - 2 + 1 := by ring
      rwa [he] at h
    have hIH := ih (k - 2) (W.Y v) hYv
    set P := casimirFactorProd W.casimir (k - 2) m with hP
    have hPX : Commute P W.X := commute_casimirFactorProd _ _ W.casimir_commute_X _ _
    have hL : ((4 : E) ^ (m + 1) • (W.X ^ (m + 1) * W.Y ^ (m + 1))) v
        = (4 : E) • W.X (((4 : E) ^ m • (W.X ^ m * W.Y ^ m)) (W.Y v)) := by
      simp only [pow_succ' (a := W.X), pow_succ (a := W.Y), LinearMap.smul_apply,
        Module.End.mul_apply, map_smul, pow_succ (a := (4 : E))]
      module
    rw [hL, hIH]
    have h1 : W.X (P (W.Y v)) = P (W.X (W.Y v)) := by
      have hc := hPX.eq
      calc W.X (P (W.Y v)) = (W.X * P) (W.Y v) := rfl
        _ = (P * W.X) (W.Y v) := by rw [← hc]
        _ = P (W.X (W.Y v)) := rfl
    rw [h1, ← map_smul, W.four_X_Y_apply k v hv]
    have h2 : W.casimir v - (((k : ℤ) : E) ^ 2) • v
        = (W.casimir - (((k : ℤ) : E) ^ 2) • (1 : Module.End E M)) v := by simp
    rw [h2, casimirFactorProd_succ]
    have h3 := (casimir_commute_factorProd W (k - 2) m ((((k : ℤ) : E)) ^ 2)).eq
    calc P ((W.casimir - (((k : ℤ) : E) ^ 2) • (1 : Module.End E M)) v)
        = (P * (W.casimir - (((k : ℤ) : E) ^ 2) • (1 : Module.End E M))) v := rfl
      _ = ((W.casimir - (((k : ℤ) : E) ^ 2) • (1 : Module.End E M)) * P) v := by rw [h3]
      _ = _ := rfl

/-- `eq:YXm_via_C` (clause `RQ2-3.04-C2`): `4^m Y^m X^m : M_{-(k+1)} → M_{-(k+1)}` equals the same
product of Casimir factors.

@census    none (auxiliary; discharges clause `RQ2-3.04-C2` of `RQ2-3.04`)
@source    prop:XY_C_relation
@clauses   RQ2-3.04-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION (arbitrary weight module over an arbitrary field), as for
`pow_X_pow_Y_eq_prod_casimir`.
-/
theorem pow_Y_pow_X_eq_prod_casimir (W : WeightData E M) (m : ℕ) (k : ℤ) (v : M)
    (hv : v ∈ W.comp (-(k + 1))) :
    ((4 : E) ^ m • (W.Y ^ m * W.X ^ m)) v = casimirFactorProd W.casimir k m v := by
  induction m generalizing k v with
  | zero => simp [casimirFactorProd_zero]
  | succ m ih =>
    have hXv : W.X v ∈ W.comp (-((k - 2) + 1)) := by
      have h := W.X_mem _ _ hv
      have he : -(k + 1) + 2 = -(k - 2 + 1) := by ring
      rwa [he] at h
    have hIH := ih (k - 2) (W.X v) hXv
    set P := casimirFactorProd W.casimir (k - 2) m with hP
    have hPY : Commute P W.Y := commute_casimirFactorProd _ _ W.casimir_commute_Y _ _
    have hL : ((4 : E) ^ (m + 1) • (W.Y ^ (m + 1) * W.X ^ (m + 1))) v
        = (4 : E) • W.Y (((4 : E) ^ m • (W.Y ^ m * W.X ^ m)) (W.X v)) := by
      simp only [pow_succ' (a := W.Y), pow_succ (a := W.X), LinearMap.smul_apply,
        Module.End.mul_apply, map_smul, pow_succ (a := (4 : E))]
      module
    rw [hL, hIH]
    have h1 : W.Y (P (W.X v)) = P (W.Y (W.X v)) := by
      have hc := hPY.eq
      calc W.Y (P (W.X v)) = (W.Y * P) (W.X v) := rfl
        _ = (P * W.Y) (W.X v) := by rw [← hc]
        _ = P (W.Y (W.X v)) := rfl
    rw [h1, ← map_smul, W.four_Y_X_apply k v hv]
    have h2 : W.casimir v - (((k : ℤ) : E) ^ 2) • v
        = (W.casimir - (((k : ℤ) : E) ^ 2) • (1 : Module.End E M)) v := by simp
    rw [h2, casimirFactorProd_succ]
    have h3 := (casimir_commute_factorProd W (k - 2) m ((((k : ℤ) : E)) ^ 2)).eq
    calc P ((W.casimir - (((k : ℤ) : E) ^ 2) • (1 : Module.End E M)) v)
        = (P * (W.casimir - (((k : ℤ) : E) ^ 2) • (1 : Module.End E M))) v := rfl
      _ = ((W.casimir - (((k : ℤ) : E) ^ 2) • (1 : Module.End E M)) * P) v := by rw [h3]
      _ = _ := rfl

/-- **Proposition** (`prop:xyscalarplusnilpotent`, census `RQ2-3.05`).  For every `m ≥ 0` and
every `k ∈ ℤ`, if `C - λ·1` acts nilpotently on `M` (clause `RQ2-3.05-H2`, the generalized
infinitesimal character `λ = ℓ²` of `RQ2-3.02`), then `4^m X^m Y^m` on `M_{k+1}` is the
**explicit** scalar `∏_{j=0}^{m-1}(ℓ² - (k-2j)²)` plus a **nilpotent** `n` (`eq:XYm_nilp`, clauses C1, C2, C5).

The companion `eq:YXm_nilp` (clauses C3, C4) is `pow_Y_pow_X_eq_scalar_add_nilpotent`.

@census    RQ2-3.05
@source    prop:xyscalarplusnilpotent
@clauses   RQ2-3.05-H1, RQ2-3.05-H2, RQ2-3.05-Hs2, RQ2-3.05-C1, RQ2-3.05-C2, RQ2-3.05-C5
@imports   none
@divergence JUSTIFIED_REFORMULATION (arbitrary weight module over an arbitrary field, disclosed),
exactly as for `pow_X_pow_Y_eq_prod_casimir`: the statement is proved for an arbitrary field `E`
and an arbitrary `WeightData E M` satisfying `RQ2-3.05-H2`, of which §3.3's `M_{L_E}` is one
instance, as the opening of tex §5.1 records (clause `Hs2`).  The existential is over the
nilpotent remainder only; the scalar is pinned explicitly, as clause `RQ2-3.05-C5` requires.
-/
theorem pow_X_pow_Y_eq_scalar_add_nilpotent (W : WeightData E M) (ℓ : ℕ)
    (hnil : IsNilpotent (W.casimir - ((ℓ : E) ^ 2) • (1 : Module.End E M)))
    (m : ℕ) (k : ℤ) :
    ∃ n : Module.End E M, IsNilpotent n ∧
      ∀ v ∈ W.comp (k + 1),
        ((4 : E) ^ m • (W.X ^ m * W.Y ^ m)) v = (nilpScalar ℓ k m E) • v + n v := by
  refine ⟨casimirFactorProd W.casimir k m - (nilpScalar ℓ k m E) • (1 : Module.End E M),
    isNilpotent_casimirRemainder W ℓ k m hnil, fun v hv => ?_⟩
  rw [pow_X_pow_Y_eq_prod_casimir W m k v hv]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  abel

/-- `eq:YXm_nilp` (clauses `RQ2-3.05-C3`, `RQ2-3.05-C4`): the same for `4^m Y^m X^m` on
`M_{-(k+1)}`, with the **same** explicit scalar and a nilpotent `n'`.

@census    none (auxiliary; discharges clauses `RQ2-3.05-C3`, `RQ2-3.05-C4` of `RQ2-3.05`)
@source    prop:xyscalarplusnilpotent
@clauses   RQ2-3.05-C3, RQ2-3.05-C4
@imports   none
@divergence JUSTIFIED_REFORMULATION (arbitrary weight module over an arbitrary field), as for
`pow_X_pow_Y_eq_scalar_add_nilpotent`.
-/
theorem pow_Y_pow_X_eq_scalar_add_nilpotent (W : WeightData E M) (ℓ : ℕ)
    (hnil : IsNilpotent (W.casimir - ((ℓ : E) ^ 2) • (1 : Module.End E M)))
    (m : ℕ) (k : ℤ) :
    ∃ n' : Module.End E M, IsNilpotent n' ∧
      ∀ v ∈ W.comp (-(k + 1)),
        ((4 : E) ^ m • (W.Y ^ m * W.X ^ m)) v = (nilpScalar ℓ k m E) • v + n' v := by
  refine ⟨casimirFactorProd W.casimir k m - (nilpScalar ℓ k m E) • (1 : Module.End E M),
    isNilpotent_casimirRemainder W ℓ k m hnil, fun v hv => ?_⟩
  rw [pow_Y_pow_X_eq_prod_casimir W m k v hv]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  abel

end Prod

section Generic

variable {E : Type u} [Field E] {M : Type v} [AddCommGroup M] [Module E M]

/-- A `List.range` product is the corresponding `Finset.range` product.

@census none
-/
theorem listProd_range_eq_finsetProd {A : Type*} [CommMonoid A] (f : ℕ → A) (n : ℕ) :
    ((List.range n).map f).prod = ∏ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]
    simp

theorem nilpScalar_eq_prod (ℓ : ℕ) (k : ℤ) (m : ℕ) :
    nilpScalar ℓ k m E
      = ∏ j ∈ Finset.range m, ((ℓ : E) ^ 2 - (((k - 2 * (j : ℤ)) : ℤ) : E) ^ 2) := by
  unfold nilpScalar
  rw [list_coe_eq_map, List.map_map, listProd_range_eq_finsetProd]
  rfl

theorem prod_range_cast_add_one (m : ℕ) :
    ∏ j ∈ Finset.range m, ((j : E) + 1) = ((Nat.factorial m : ℕ) : E) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    push_cast
    ring

theorem prod_range_cast_sub (m : ℕ) :
    ∏ j ∈ Finset.range m, ((m : E) - (j : E)) = ((Nat.factorial m : ℕ) : E) := by
  rw [← prod_range_cast_add_one (E := E) m, ← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have h : ((m - 1 - j : ℕ) : E) = (m : E) - 1 - (j : E) := by
    have h1 : (j : ℕ) ≤ m - 1 := by omega
    have h2 : (1 : ℕ) ≤ m := by omega
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    ring
  rw [h]
  ring

theorem nilpScalar_gammaStar (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    nilpScalar ℓ ((ℓ : ℤ) - 2) (ℓ - 1) E
      = (4 : E) ^ (ℓ - 1) * ((Nat.factorial (ℓ - 1) : ℕ) : E) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [nilpScalar_eq_prod]
  have hfac : ∀ j ∈ Finset.range m,
      (((m + 1 : ℕ) : E) ^ 2 - ((((m + 1 : ℕ) : ℤ) - 2 - 2 * (j : ℤ) : ℤ) : E) ^ 2)
        = 4 * (((j : E) + 1) * ((m : E) - (j : E))) := by
    intro j _
    push_cast
    ring
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_range, prod_range_cast_add_one, prod_range_cast_sub]
  ring

variable {M : Type v} [AddCommGroup M] [Module E M]

-- `WeightData.casimir_mem_comp` (`C` preserves `M_n`) lives in `HC/Graded.lean`.

theorem casimirFactorProd_mem_comp (W : WeightData E M) (k : ℤ) (m : ℕ) (n : ℤ) (v : M)
    (hv : v ∈ W.comp n) : casimirFactorProd W.casimir k m v ∈ W.comp n := by
  induction m generalizing k with
  | zero => rw [casimirFactorProd_zero]; simpa using hv
  | succ m ih =>
    rw [casimirFactorProd_succ]
    have hP := ih (k - 2)
    show (W.casimir - _ • (1 : Module.End E M)) (casimirFactorProd W.casimir (k - 2) m v) ∈ _
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact sub_mem (W.casimir_mem_comp n _ hP) (Submodule.smul_mem _ _ hP)

theorem WeightData.pow_X_mem (W : WeightData E M) (r : ℕ) (n : ℤ) (v : M) (hv : v ∈ W.comp n) :
    (W.X ^ r) v ∈ W.comp (n + 2 * r) := by
  induction r with
  | zero => simpa using hv
  | succ r ih =>
    have h := W.X_mem _ _ ih
    have he : n + 2 * (r : ℤ) + 2 = n + 2 * ((r : ℤ) + 1) := by ring
    rw [he] at h
    rw [pow_succ' (a := W.X)]
    push_cast
    exact h

theorem WeightData.pow_Y_mem (W : WeightData E M) (r : ℕ) (n : ℤ) (v : M) (hv : v ∈ W.comp n) :
    (W.Y ^ r) v ∈ W.comp (n - 2 * r) := by
  induction r with
  | zero => simpa using hv
  | succ r ih =>
    have h := W.Y_mem _ _ ih
    have he : n - 2 * (r : ℤ) - 2 = n - 2 * ((r : ℤ) + 1) := by ring
    rw [he] at h
    rw [pow_succ' (a := W.Y)]
    push_cast
    exact h

end Generic

/-! ## Steps O-3/O-4 — `cor:X_Y_inverses`, `cor:T_operators`, `def:xstarystar` over every field

Stated for an arbitrary `W : WeightData F M` over a field `F` of characteristic `0` with the
generalized infinitesimal character `λ = ℓ²` as the hypothesis `hgic`.  The remainders `n`, `n̄`
of `eq:XY_inverses_rel` are the **named** operator `W.normRemainder ℓ`, a polynomial in `C`, the
same operator on `M_{ℓ-1}` and on `M_{-(ℓ-1)}`. -/

namespace WeightData

section Normalizations

variable {F : Type u} [Field F] {M : Type v} [AddCommGroup M] [Module F M]

/-- `γ_⋆ = (ℓ-1)!` inside `F` (clause `RQ2-3.06-C7`).

@census none
-/
noncomputable def gammaStar (F : Type u) [Field F] (ℓ : ℕ) : F := ((Nat.factorial (ℓ - 1) : ℕ) : F)

/-- @census none -/
theorem gammaStar_eq (ℓ : ℕ) : gammaStar F ℓ = ((Nat.factorial (ℓ - 1) : ℕ) : F) := rfl

/-- `γ_⋆ ≠ 0` in characteristic `0`.  @census none -/
theorem gammaStar_ne_zero [CharZero F] (ℓ : ℕ) : gammaStar F ℓ ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

/-- `4^m ≠ 0` in characteristic `0`.  @census none -/
theorem four_pow_ne_zero [CharZero F] (m : ℕ) : ((4 : F) ^ m) ≠ 0 :=
  pow_ne_zero _ (by norm_num)

/-- A unit of `End_F(N)` is bijective.  @census none -/
theorem bijective_of_isUnit_end {N : Type*} [AddCommGroup N] [Module F N]
    {g : Module.End F N} (hg : IsUnit g) : Function.Bijective g := by
  obtain ⟨u, rfl⟩ := hg
  constructor
  · intro a b hab
    have h := congrArg (fun w => (u.inv : Module.End F N) w) hab
    simpa only [← Module.End.mul_apply, u.inv_val, Module.End.one_apply] using h
  · intro b
    refine ⟨(u.inv : Module.End F N) b, ?_⟩
    have : ((u : Module.End F N) * u.inv) b = b := by rw [u.val_inv]; rfl
    simpa only [Module.End.mul_apply] using this

/-- A map agreeing on a submodule `P` with `c·1 + n`, `c ≠ 0`, `n` nilpotent and preserving `P`,
is a bijection of `P` (the step "`γ_⋆² ≠ 0` and `n` nilpotent, so the composite is invertible").

@census none
-/
theorem bijOn_scalar_add_nilpotent (P : Submodule F M) (c : F) (hc : c ≠ 0)
    (nn : Module.End F M) (hnil : IsNilpotent nn) (hmaps : ∀ v ∈ P, nn v ∈ P)
    (f : M → M) (hf : ∀ v ∈ P, f v = c • v + nn v) :
    Set.BijOn f ↑P ↑P := by
  set A : Module.End F M := c • 1 + nn with hA
  have hAmaps : ∀ v ∈ P, A v ∈ P := by
    intro v hv
    show (c • (1 : Module.End F M) + nn) v ∈ P
    rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact add_mem (Submodule.smul_mem _ _ hv) (hmaps v hv)
  have hnP : IsNilpotent (LinearMap.restrict nn hmaps) := Module.End.isNilpotent.restrict hmaps hnil
  have hres : LinearMap.restrict A hAmaps = c • 1 + LinearMap.restrict nn hmaps := by
    ext w
    show ((A w.1 : M)) = _
    simp [hA, LinearMap.restrict_apply]
  have hunit : IsUnit (LinearMap.restrict A hAmaps) := by
    rw [hres]
    have hfac : (c • (1 : Module.End F P) + LinearMap.restrict nn hmaps)
        = (c • (1 : Module.End F P)) * (1 + c⁻¹ • LinearMap.restrict nn hmaps) := by
      rw [mul_add, mul_one, smul_mul_assoc, one_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [hfac]
    exact (Unipotent.isUnit_smul_one_end hc).mul
      (Unipotent.isUnit_one_add_of_isNilpotent (hnP.smul c⁻¹))
  have hbij : Set.BijOn A ↑P ↑P := by
    have hb := bijective_of_isUnit_end hunit
    refine ⟨fun v hv => hAmaps v hv, ?_, ?_⟩
    · intro a ha b hb' hab
      have := hb.1 (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb'⟩) (by apply Subtype.ext; simpa using hab)
      exact congrArg Subtype.val this
    · intro b hb'
      obtain ⟨a, ha⟩ := hb.2 ⟨b, hb'⟩
      exact ⟨a.1, a.2, congrArg Subtype.val ha⟩
  refine hbij.congr ?_
  intro v hv
  rw [hf v hv]
  show _ = (c • (1 : Module.End F M) + nn) v
  rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]

/-- The scalar `∏(ℓ² - (k-2j)²)` is fixed by every ring endomorphism (it is an integer), in
particular by every `σ ∈ G_E`.

@census none
-/
theorem ringHom_nilpScalar {G : Type*} [FunLike G F F] [RingHomClass G F F] (f : G) (ℓ : ℕ)
    (k : ℤ) (m : ℕ) : f (nilpScalar ℓ k m F) = nilpScalar ℓ k m F := by
  induction m generalizing k with
  | zero => rw [nilpScalar_zero, map_one]
  | succ m ih =>
    rw [nilpScalar_succ, map_mul, ih, map_sub, map_pow, map_pow, map_natCast, map_intCast]

variable [CharZero F] {ℓ : ℕ}

/-- The generalized infinitesimal character `λ = ℓ²` (`RQ2-3.02`) in the form `§3.3` uses:
`C - ℓ²·1` acts nilpotently.

@census none
-/
theorem gic_nilpotent (W : WeightData F M) (hgic : HasGeneralizedInfinitesimalCharacter W ℓ) :
    IsNilpotent (W.casimir - ((ℓ : F) ^ 2) • (1 : Module.End F M)) := by
  have h : IsNilpotent (W.casimir
      - (algebraMap ℚ F ((ℓ : ℚ) ^ 2)) • (1 : Module.End F M)) := hgic
  have he : (algebraMap ℚ F ((ℓ : ℚ) ^ 2)) = ((ℓ : F)) ^ 2 := by
    rw [map_pow, map_natCast]
  rwa [he] at h

variable (ℓ) in
/-- The remainder `n = n̄ = (4^{ℓ-1})⁻¹ · (∏_{j<ℓ-1}(C - (ℓ-2-2j)²) - 4^{ℓ-1}γ_⋆²·1)` of
`eq:XY_inverses_rel` (the scalar part is `nilpScalar_gammaStar`): a polynomial in the Casimir,
the **same** operator on `M_{ℓ-1}` and `M_{-(ℓ-1)}`, which is why it commutes with every
`σ ∈ G_E` (`HC.galAct_normRemainder`).

@census none
-/
noncomputable def normRemainder (W : WeightData F M) : Module.End F M :=
  (((4 : F) ^ (ℓ - 1))⁻¹) •
    (casimirFactorProd W.casimir ((ℓ : ℤ) - 2) (ℓ - 1)
      - (nilpScalar ℓ ((ℓ : ℤ) - 2) (ℓ - 1) F) • 1)

/-- `n` is nilpotent (from `prop:xyscalarplusnilpotent`'s named remainder).  @census none -/
theorem isNilpotent_normRemainder (W : WeightData F M)
    (hgic : HasGeneralizedInfinitesimalCharacter W ℓ) : IsNilpotent (W.normRemainder ℓ) :=
  (isNilpotent_casimirRemainder W ℓ ((ℓ : ℤ) - 2) (ℓ - 1) (W.gic_nilpotent hgic)).smul _

omit [CharZero F] in
/-- @census none -/
theorem normRemainder_apply (W : WeightData F M) (v : M) :
    W.normRemainder ℓ v = (((4 : F) ^ (ℓ - 1))⁻¹) •
      (casimirFactorProd W.casimir ((ℓ : ℤ) - 2) (ℓ - 1) v
        - (nilpScalar ℓ ((ℓ : ℤ) - 2) (ℓ - 1) F) • v) := by
  rw [normRemainder, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply]

omit [CharZero F] in
/-- `n` preserves every `M_n`.  @census none -/
theorem normRemainder_mem_comp (W : WeightData F M) (n : ℤ) (v : M)
    (hv : v ∈ W.comp n) : W.normRemainder ℓ v ∈ W.comp n := by
  rw [normRemainder_apply]
  exact Submodule.smul_mem _ _
    (sub_mem (casimirFactorProd_mem_comp W _ _ n v hv) (Submodule.smul_mem _ _ hv))

/-- **Corollary** (`cor:X_Y_inverses`, census `RQ2-3.06`).  For `ℓ ≥ 1` and `M` with generalized
infinitesimal character `λ = ℓ²`, the maps `X^{ℓ-1} : M_{-(ℓ-1)} → M_{ℓ-1}` (clause `C1`) and
`Y^{ℓ-1} : M_{ℓ-1} → M_{-(ℓ-1)}` (clause `C2`) are **invertible**, and
`X^{ℓ-1} ∘ Y^{ℓ-1} = γ_⋆²·1 + n` on `M_{ℓ-1}` (clause `C3`), `Y^{ℓ-1} ∘ X^{ℓ-1} = γ_⋆²·1 + n̄` on
`M_{-(ℓ-1)}` (clause `C4`), with `n = n̄ = W.normRemainder ℓ` nilpotent (clauses `C5`, `C8`) and
`γ_⋆ = (ℓ-1)!` explicitly (clause `C7`, `gammaStar`).  The proof is the source's: the scalar part
of `eq:XYm_nilp` at `m = ℓ-1`, `k = ℓ-2` is `4^{ℓ-1}γ_⋆²` (`nilpScalar_gammaStar`), and the two
composites, being `γ_⋆²·1 + n`, are invertible, whence surjectivity/injectivity of both factors.
The conjugacy clause `C6` is `HC.galAct_normRemainder_of_chi_neg_one` (for `c`, by the source's
argument) and `HC.galAct_normRemainder` (every `σ ∈ G_E`).

@census    RQ2-3.06
@source    cor:X_Y_inverses
@clauses   RQ2-3.06-H1, RQ2-3.06-H2, RQ2-3.06-Hs1, RQ2-3.06-Hs2, RQ2-3.06-C1, RQ2-3.06-C2,
  RQ2-3.06-C3, RQ2-3.06-C4, RQ2-3.06-C5, RQ2-3.06-C7, RQ2-3.06-C8
@imports   none
@divergence JUSTIFIED_REFORMULATION (arbitrary weight module; invertibility on weight spaces).
(1) Clauses `H2`/`Hs1` take `M_E ∈ HC_λ(𝔤,K)_E` and its base change `M_{L_E}`; this statement is
proved for an arbitrary `W : WeightData F M` over any field `F` of characteristic `0` with the
generalized infinitesimal character `λ = ℓ²` (`hgic`), as the opening of tex §5.1 records
(clause `Hs2`): the proof uses only `C = H² - 2H + 4XY + 1`, `H|_{M_n} = n`, `[C,X] = [C,Y] = 0`,
`C - ℓ²` nilpotent and `4, γ_⋆ ≠ 0`.  `M_{L_E}` with its `L_E`-weight data is an instance
(`HC.weight`), so the statement is stronger than the source's.  (2) "Invertible as a map
`M_{∓(ℓ-1)} → M_{±(ℓ-1)}`" is `Set.BijOn` between the weight submodules; `n`, `n̄` are the single
explicit operator `normRemainder` on `M`, whose restrictions to `M_{ℓ-1}`, `M_{-(ℓ-1)}` are the
source's `n`, `n̄` (it preserves each `M_n`, `normRemainder_mem_comp`).
-/
theorem isUnit_pow_X (W : WeightData F M) (hgic : HasGeneralizedInfinitesimalCharacter W ℓ)
    (hℓ : 1 ≤ ℓ) :
    Set.BijOn (W.X ^ (ℓ - 1)) (W.comp (-((ℓ : ℤ) - 1))) (W.comp ((ℓ : ℤ) - 1))
      ∧ Set.BijOn (W.Y ^ (ℓ - 1)) (W.comp ((ℓ : ℤ) - 1)) (W.comp (-((ℓ : ℤ) - 1)))
      ∧ IsNilpotent (W.normRemainder ℓ)
      ∧ (∀ v ∈ W.comp ((ℓ : ℤ) - 1),
          (W.X ^ (ℓ - 1) * W.Y ^ (ℓ - 1)) v = gammaStar F ℓ ^ 2 • v + W.normRemainder ℓ v)
      ∧ (∀ v ∈ W.comp (-((ℓ : ℤ) - 1)),
          (W.Y ^ (ℓ - 1) * W.X ^ (ℓ - 1)) v = gammaStar F ℓ ^ 2 • v + W.normRemainder ℓ v) := by
  have hmz : ((ℓ - 1 : ℕ) : ℤ) = (ℓ : ℤ) - 1 := by omega
  have hγ : gammaStar F ℓ ≠ 0 := gammaStar_ne_zero ℓ
  have hγ2 : gammaStar F ℓ ^ 2 ≠ 0 := pow_ne_zero _ hγ
  have hsc : nilpScalar ℓ ((ℓ : ℤ) - 2) (ℓ - 1) F = (4 : F) ^ (ℓ - 1) * gammaStar F ℓ ^ 2 := by
    rw [nilpScalar_gammaStar ℓ hℓ, gammaStar_eq]
  have h4 : (((4 : F) ^ (ℓ - 1))⁻¹ * ((4 : F) ^ (ℓ - 1) * gammaStar F ℓ ^ 2))
      = gammaStar F ℓ ^ 2 := by
    rw [← mul_assoc, inv_mul_cancel₀ (four_pow_ne_zero _), one_mul]
  have hXY : ∀ v ∈ W.comp ((ℓ : ℤ) - 1),
      (W.X ^ (ℓ - 1) * W.Y ^ (ℓ - 1)) v = gammaStar F ℓ ^ 2 • v + W.normRemainder ℓ v := by
    intro v hv
    have hv' : v ∈ W.comp (((ℓ : ℤ) - 2) + 1) := by
      have he : ((ℓ : ℤ) - 2) + 1 = (ℓ : ℤ) - 1 := by ring
      rwa [he]
    have h := pow_X_pow_Y_eq_prod_casimir W (ℓ - 1) ((ℓ : ℤ) - 2) v hv'
    rw [LinearMap.smul_apply] at h
    rw [normRemainder_apply, hsc, ← h, smul_sub, smul_smul, smul_smul,
      inv_mul_cancel₀ (four_pow_ne_zero (ℓ - 1)), one_smul, h4]
    abel
  have hYX : ∀ v ∈ W.comp (-((ℓ : ℤ) - 1)),
      (W.Y ^ (ℓ - 1) * W.X ^ (ℓ - 1)) v = gammaStar F ℓ ^ 2 • v + W.normRemainder ℓ v := by
    intro v hv
    have hv' : v ∈ W.comp (-(((ℓ : ℤ) - 2) + 1)) := by
      have he : -(((ℓ : ℤ) - 2) + 1) = -((ℓ : ℤ) - 1) := by ring
      rwa [he]
    have h := pow_Y_pow_X_eq_prod_casimir W (ℓ - 1) ((ℓ : ℤ) - 2) v hv'
    rw [LinearMap.smul_apply] at h
    rw [normRemainder_apply, hsc, ← h, smul_sub, smul_smul, smul_smul,
      inv_mul_cancel₀ (four_pow_ne_zero (ℓ - 1)), one_smul, h4]
    abel
  have hXmaps : ∀ v ∈ W.comp (-((ℓ : ℤ) - 1)), (W.X ^ (ℓ - 1)) v ∈ W.comp ((ℓ : ℤ) - 1) := by
    intro v hv
    have h := W.pow_X_mem (ℓ - 1) (-((ℓ : ℤ) - 1)) v hv
    have he : -((ℓ : ℤ) - 1) + 2 * ((ℓ - 1 : ℕ) : ℤ) = (ℓ : ℤ) - 1 := by rw [hmz]; ring
    rwa [he] at h
  have hYmaps : ∀ v ∈ W.comp ((ℓ : ℤ) - 1), (W.Y ^ (ℓ - 1)) v ∈ W.comp (-((ℓ : ℤ) - 1)) := by
    intro v hv
    have h := W.pow_Y_mem (ℓ - 1) ((ℓ : ℤ) - 1) v hv
    have he : (ℓ : ℤ) - 1 - 2 * ((ℓ - 1 : ℕ) : ℤ) = -((ℓ : ℤ) - 1) := by rw [hmz]; ring
    rwa [he] at h
  have hnil := W.isNilpotent_normRemainder hgic
  have hbXY : Set.BijOn (fun v => (W.X ^ (ℓ - 1) * W.Y ^ (ℓ - 1)) v)
      ↑(W.comp ((ℓ : ℤ) - 1)) ↑(W.comp ((ℓ : ℤ) - 1)) :=
    bijOn_scalar_add_nilpotent _ _ hγ2 _ hnil (W.normRemainder_mem_comp _) _ hXY
  have hbYX : Set.BijOn (fun v => (W.Y ^ (ℓ - 1) * W.X ^ (ℓ - 1)) v)
      ↑(W.comp (-((ℓ : ℤ) - 1))) ↑(W.comp (-((ℓ : ℤ) - 1))) :=
    bijOn_scalar_add_nilpotent _ _ hγ2 _ hnil (W.normRemainder_mem_comp _) _ hYX
  refine ⟨⟨hXmaps, ?_, ?_⟩, ⟨hYmaps, ?_, ?_⟩, hnil, hXY, hYX⟩
  · intro a ha b hb hab
    refine hbYX.2.1 ha hb ?_
    simp only [Module.End.mul_apply]
    rw [hab]
  · intro u hu
    obtain ⟨v, hv, hvu⟩ := hbXY.2.2 hu
    exact ⟨(W.Y ^ (ℓ - 1)) v, hYmaps v hv, by rw [← Module.End.mul_apply]; exact hvu⟩
  · intro a ha b hb hab
    refine hbXY.2.1 ha hb ?_
    simp only [Module.End.mul_apply]
    rw [hab]
  · intro u hu
    obtain ⟨v, hv, hvu⟩ := hbYX.2.2 hu
    exact ⟨(W.X ^ (ℓ - 1)) v, hXmaps v hv, by rw [← Module.End.mul_apply]; exact hvu⟩

variable (ℓ) in
/-- `T_+ := (4^{ℓ-1}·γ_⋆²)^{-1} · ∏_{j=0}^{ℓ-2} (C - (ℓ-2-2j)²·1)` (`eq:T_plus_def`, clause
`RQ2-3.07-C1`), as an endomorphism of `M`; `Tplus_isUnit` restricts it to `M_{ℓ+1}`.  As elements
of `U(𝔤)`, `T_+` and `T_-` are the same product; the source names them by the space they act on.

@census    none (auxiliary; discharges clause `RQ2-3.07-C1` of `RQ2-3.07`)
@source    cor:T_operators
@clauses   RQ2-3.07-C1
@imports   none
@divergence JUSTIFIED_REFORMULATION (arbitrary weight module), as for `isUnit_pow_X`: stated for
any `W : WeightData F M` over a field of characteristic `0` with `λ = ℓ²` instead of the base
change `M_{L_E}` of `M_E ∈ HC_λ(𝔤,K)_E` (tex §5.1 opening, clause `Hs2`); stronger than the
source's statement.
-/
noncomputable def Tplus (W : WeightData F M) : Module.End F M :=
  ((4 : F) ^ (ℓ - 1) * gammaStar F ℓ ^ 2)⁻¹ • casimirFactorProd W.casimir ((ℓ : ℤ) - 2) (ℓ - 1)

variable (ℓ) in
/-- `T_- := (4^{ℓ-1}·γ_⋆²)^{-1} · ∏_{j=0}^{ℓ-2} (C - (ℓ-2-2j)²·1)` (`eq:T_minus_def`, clause
`RQ2-3.07-C2`); `Tplus_isUnit` restricts it to `M_{-(ℓ+1)}`.

@census    none (auxiliary; discharges clause `RQ2-3.07-C2` of `RQ2-3.07`)
@source    cor:T_operators
@clauses   RQ2-3.07-C2,
           RQ2-5.12-S-O4
@imports   none
@divergence JUSTIFIED_REFORMULATION (arbitrary weight module), as for `isUnit_pow_X`: stated for
any `W : WeightData F M` over a field of characteristic `0` with `λ = ℓ²` instead of the base
change `M_{L_E}` of `M_E ∈ HC_λ(𝔤,K)_E` (tex §5.1 opening, clause `Hs2`); stronger than the
source's statement.
-/
noncomputable def Tminus (W : WeightData F M) : Module.End F M :=
  ((4 : F) ^ (ℓ - 1) * gammaStar F ℓ ^ 2)⁻¹ • casimirFactorProd W.casimir ((ℓ : ℤ) - 2) (ℓ - 1)

/-- **Corollary** (`cor:T_operators`, census `RQ2-3.07`).  For `ℓ ≥ 1`, `γ_⋆ = (ℓ-1)!` (clause
`H1`) and `C - λ·1` nilpotent (clause `Hs1`, `hgic`), `T_+` and `T_-` are **automorphisms** of
`M_{ℓ+1}` resp. `M_{-(ℓ+1)}` (clause `C3`), and `T_± = 1 + n_±` there with `n_±` **nilpotent**
(clause `C4`).  The proof is the source's: the scalar part of the product is `4^{ℓ-1}γ_⋆²`
(`nilpScalar_gammaStar`), exactly the factor normalized away.

@census    RQ2-3.07
@source    cor:T_operators
@clauses   RQ2-3.07-H1, RQ2-3.07-Hs1, RQ2-3.07-Hs2, RQ2-3.07-C3, RQ2-3.07-C4
@imports   none
@divergence JUSTIFIED_REFORMULATION (arbitrary weight module; automorphism as `Set.BijOn`), as for
`isUnit_pow_X`: stated for any `W : WeightData F M` over a field of characteristic `0` with
`λ = ℓ²` instead of the base change `M_{L_E}` of `M_E ∈ HC_λ(𝔤,K)_E` (tex §5.1 opening, clause
`Hs2`); "automorphism of `M_{±(ℓ+1)}`" is `Set.BijOn` of the endomorphism of `M` on that weight
submodule, and `T_± = 1 + n_±` is asserted on it.
-/
theorem Tplus_isUnit (W : WeightData F M) (hgic : HasGeneralizedInfinitesimalCharacter W ℓ)
    (hℓ : 1 ≤ ℓ) :
    Set.BijOn (W.Tplus ℓ) (W.comp ((ℓ : ℤ) + 1)) (W.comp ((ℓ : ℤ) + 1))
      ∧ Set.BijOn (W.Tminus ℓ) (W.comp (-((ℓ : ℤ) + 1))) (W.comp (-((ℓ : ℤ) + 1)))
      ∧ ∃ nplus nminus : Module.End F M, IsNilpotent nplus ∧ IsNilpotent nminus
          ∧ (∀ v ∈ W.comp ((ℓ : ℤ) + 1), W.Tplus ℓ v = v + nplus v)
          ∧ (∀ v ∈ W.comp (-((ℓ : ℤ) + 1)), W.Tminus ℓ v = v + nminus v) := by
  have hγ2 : gammaStar F ℓ ^ 2 ≠ 0 := pow_ne_zero _ (gammaStar_ne_zero ℓ)
  have hden : ((4 : F) ^ (ℓ - 1) * gammaStar F ℓ ^ 2) ≠ 0 :=
    mul_ne_zero (four_pow_ne_zero _) hγ2
  have hsc : nilpScalar ℓ ((ℓ : ℤ) - 2) (ℓ - 1) F = (4 : F) ^ (ℓ - 1) * gammaStar F ℓ ^ 2 := by
    rw [nilpScalar_gammaStar ℓ hℓ, gammaStar_eq]
  set nT : Module.End F M :=
    ((4 : F) ^ (ℓ - 1) * gammaStar F ℓ ^ 2)⁻¹ •
      (casimirFactorProd W.casimir ((ℓ : ℤ) - 2) (ℓ - 1)
        - (nilpScalar ℓ ((ℓ : ℤ) - 2) (ℓ - 1) F) • 1) with hnTdef
  have hnil : IsNilpotent nT :=
    (isNilpotent_casimirRemainder W ℓ ((ℓ : ℤ) - 2) (ℓ - 1) (W.gic_nilpotent hgic)).smul _
  have hmem : ∀ (n : ℤ), ∀ v ∈ W.comp n, nT v ∈ W.comp n := by
    intro n v hv
    rw [hnTdef, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    exact Submodule.smul_mem _ _
      (sub_mem (casimirFactorProd_mem_comp W _ _ n v hv) (Submodule.smul_mem _ _ hv))
  have hT : ∀ v : M, W.Tplus ℓ v = v + nT v := by
    intro v
    rw [Tplus, hnTdef, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, smul_sub, smul_smul, hsc,
      inv_mul_cancel₀ hden, one_smul]
    abel
  have hTm : ∀ v : M, W.Tminus ℓ v = v + nT v := by
    intro v
    rw [Tminus, hnTdef, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, smul_sub, smul_smul, hsc,
      inv_mul_cancel₀ hden, one_smul]
    abel
  refine ⟨?_, ?_, nT, nT, hnil, hnil, fun v _ => hT v, fun v _ => hTm v⟩
  · exact bijOn_scalar_add_nilpotent _ 1 one_ne_zero nT hnil (hmem _) _
      (fun v _ => by rw [hT v, one_smul])
  · exact bijOn_scalar_add_nilpotent _ 1 one_ne_zero nT hnil (hmem _) _
      (fun v _ => by rw [hTm v, one_smul])

variable (ℓ) in
/-- **Definition** (`def:xstarystar`, census `RQ2-3.08`): `X_⋆ := γ_⋆^{-1} · X^{ℓ-1}`, to be
restricted to `M_{-(ℓ-1)}` (clause `C1`, for `ℓ ≥ 1`, clause `H1`, under `cor:X_Y_inverses`).
The companion `Y_⋆` (clause `C2`) is `yStar`; the relations (clauses `C3`–`C5`) are
`xStar_yStar_relations` and `HC.galAct_nStar`.

@census    RQ2-3.08
@source    def:xstarystar
@clauses   RQ2-3.08-H1, RQ2-3.08-C1,
           RQ2-5.12-S-O4
@imports   none
@divergence JUSTIFIED_REFORMULATION (arbitrary weight module; restriction left to use sites): the
operator is defined on all of `M` for any `W : WeightData F M`, and "`|_{M_{-(ℓ-1)}}`" is applied
where it is used (`xStar_yStar_relations` quantifies over `v ∈ M_{-(ℓ-1)}`), since `X^{ℓ-1}` maps
`M_{-(ℓ-1)}` into `M_{ℓ-1}` (`isUnit_pow_X`); the base-change setup is generalized as in
`isUnit_pow_X` (tex §5.1 opening).
-/
noncomputable def xStar (W : WeightData F M) : Module.End F M :=
  (gammaStar F ℓ)⁻¹ • W.X ^ (ℓ - 1)

variable (ℓ) in
/-- `Y_⋆ := γ_⋆^{-1} · Y^{ℓ-1}`, to be restricted to `M_{ℓ-1}` (clause `RQ2-3.08-C2`).

@census    none (auxiliary; discharges clause `RQ2-3.08-C2` of `RQ2-3.08`)
@source    def:xstarystar
@clauses   RQ2-3.08-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION (arbitrary weight module; restriction left to use sites), as
for `xStar`.
-/
noncomputable def yStar (W : WeightData F M) : Module.End F M :=
  (gammaStar F ℓ)⁻¹ • W.Y ^ (ℓ - 1)

omit [CharZero F] in
/-- `X_⋆ Y_⋆ = γ_⋆^{-2}·X^{ℓ-1}Y^{ℓ-1}`.  @census none -/
theorem xStar_mul_yStar (W : WeightData F M) :
    W.xStar ℓ * W.yStar ℓ = (gammaStar F ℓ ^ 2)⁻¹ • (W.X ^ (ℓ - 1) * W.Y ^ (ℓ - 1)) := by
  rw [xStar, yStar, smul_mul_smul_comm, ← mul_inv, ← sq]

omit [CharZero F] in
/-- `Y_⋆ X_⋆ = γ_⋆^{-2}·Y^{ℓ-1}X^{ℓ-1}`.  @census none -/
theorem yStar_mul_xStar (W : WeightData F M) :
    W.yStar ℓ * W.xStar ℓ = (gammaStar F ℓ ^ 2)⁻¹ • (W.Y ^ (ℓ - 1) * W.X ^ (ℓ - 1)) := by
  rw [xStar, yStar, smul_mul_smul_comm, ← mul_inv, ← sq]

/-- The relations after `def:xstarystar` (clauses `RQ2-3.08-C3`, `C4`, `C5`):
`X_⋆ Y_⋆ = 1_{M_{ℓ-1}} + n_⋆` and `Y_⋆ X_⋆ = 1_{M_{-(ℓ-1)}} + n̄_⋆`, where
`n_⋆ = n̄_⋆ = γ_⋆^{-2}·n` is the explicit rescaling of `cor:X_Y_inverses`'s remainder and is
nilpotent.  The conjugacy half of `C5` is `HC.galAct_nStar`.

@census    none (auxiliary; discharges clauses `RQ2-3.08-C3`, `RQ2-3.08-C4`, `RQ2-3.08-C5` of `RQ2-3.08`)
@source    def:xstarystar
@clauses   RQ2-3.08-C3, RQ2-3.08-C4, RQ2-3.08-C5
@imports   none
@divergence WEAKENED_OR_PARTIAL (the conjugacy half of `C5` is a separate declaration) and
JUSTIFIED_REFORMULATION (arbitrary weight module, as for `isUnit_pow_X`).  This declaration states
the two relations and the nilpotence of `n_⋆`, `n̄_⋆`; "conjugate to each other if `√-1 ∉ E`" needs
the Galois action and is `HC.galAct_nStar` on `A : HC ℓ E D`.
-/
theorem xStar_yStar_relations (W : WeightData F M)
    (hgic : HasGeneralizedInfinitesimalCharacter W ℓ) (hℓ : 1 ≤ ℓ) :
    IsNilpotent ((gammaStar F ℓ ^ 2)⁻¹ • W.normRemainder ℓ)
      ∧ (∀ v ∈ W.comp ((ℓ : ℤ) - 1),
          (W.xStar ℓ * W.yStar ℓ) v = v + ((gammaStar F ℓ ^ 2)⁻¹ • W.normRemainder ℓ) v)
      ∧ (∀ v ∈ W.comp (-((ℓ : ℤ) - 1)),
          (W.yStar ℓ * W.xStar ℓ) v = v + ((gammaStar F ℓ ^ 2)⁻¹ • W.normRemainder ℓ) v) := by
  have hγ2 : gammaStar F ℓ ^ 2 ≠ 0 := pow_ne_zero _ (gammaStar_ne_zero ℓ)
  obtain ⟨-, -, hnil, hn, hnbar⟩ := W.isUnit_pow_X hgic hℓ
  refine ⟨hnil.smul _, ?_, ?_⟩
  · intro v hv
    rw [xStar_mul_yStar, LinearMap.smul_apply, hn v hv, LinearMap.smul_apply, smul_add, smul_smul,
      inv_mul_cancel₀ hγ2, one_smul]
  · intro v hv
    rw [yStar_mul_xStar, LinearMap.smul_apply, hnbar v hv, LinearMap.smul_apply, smul_add,
      smul_smul, inv_mul_cancel₀ hγ2, one_smul]


end Normalizations

end WeightData

section GalAct

set_option linter.dupNamespace false

variable {E : Type} [Field E] [CharZero E] {D : ImagUnit E} {ℓ : ℕ}

namespace HC

/-- **`C` is `G_E`-invariant on `M_{L_E}`**: `σ(Cv) = C(σv)` for every `σ ∈ G_E` — by
`WeightData.casimir_conj` (`cC = C`, `prop:casimirdescends`) when `χ_E(σ) = -1`, trivially when
`σ = 1`.  Used by `galAct_normRemainder`.

@census none
-/
theorem galAct_casimir (A : HC ℓ E D) (σ : D.L ≃ₐ[E] D.L) (v : A.carrier) :
    A.galAct σ (A.weight.casimir v) = A.weight.casimir (A.galAct σ v) := by
  rcases D.chi_cases σ with hσ | hσ
  · rw [A.galAct_of_chi_one hσ, A.galAct_of_chi_one hσ]
  · obtain ⟨-, hX, hY, hH⟩ := A.compat_neg hσ
    exact A.weight.casimir_conj (A.galAct σ).toAddMonoidHom hX hY hH v

/-- `σ` commutes with `∏(C - (k-2j)²·1)` (integer scalars are `σ`-fixed).  @census none -/
theorem galAct_casimirFactorProd (A : HC ℓ E D) (σ : D.L ≃ₐ[E] D.L) (k : ℤ) (m : ℕ)
    (v : A.carrier) :
    A.galAct σ (casimirFactorProd A.weight.casimir k m v)
      = casimirFactorProd A.weight.casimir k m (A.galAct σ v) := by
  induction m generalizing k v with
  | zero => rw [casimirFactorProd_zero]; rfl
  | succ m ih =>
    rw [casimirFactorProd_succ, Module.End.mul_apply, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
      Module.End.one_apply, map_sub, A.galAct_casimir, galActOf_smul, map_pow, map_intCast, ih]

/-- **The conjugacy clause of `cor:X_Y_inverses`** (`RQ2-3.06-C6`): `σ ∘ n = n̄ ∘ σ` for every
`σ ∈ G_E`, with `n = n̄ = A.weight.normRemainder ℓ` the remainders of `WeightData.isUnit_pow_X`.

@census    none (auxiliary; discharges clause `RQ2-3.06-C6` of `RQ2-3.06`)
@source    cor:X_Y_inverses
@clauses   RQ2-3.06-C6
@imports   none
@divergence JUSTIFIED_REFORMULATION (every `σ ∈ G_E`; `n̄ = n`).  The source states the clause
"if `√-1 ∉ E`" for the complex conjugation `c`; here it is stated for **every** `σ ∈ G_E`, which
is `{1, c}` if `√-1 ∉ E` and trivial (`galAct_of_chi_one`) if `√-1 ∈ E`, so the two readings
agree.  `n` and `n̄` are the same operator `WeightData.normRemainder`, so "`c ∘ n = n̄ ∘ c`" reads
`σ ∘ n = n ∘ σ`.  **Proof route** (not the source's): `n` is a polynomial in `C` with rational
coefficients, `C` is `σ`-invariant (`galAct_casimir`, from `cC = C`) and rational scalars are
`σ`-fixed (`galAct_casimirFactorProd`, `ringHom_nilpScalar`).  The source's route — `cX = Yc`,
`cY = Xc` carry `X^{ℓ-1}Y^{ℓ-1}` to `Y^{ℓ-1}X^{ℓ-1}` — is `galAct_normRemainder_of_chi_neg_one`.
-/
theorem galAct_normRemainder (A : HC ℓ E D) (σ : D.L ≃ₐ[E] D.L) (v : A.carrier) :
    A.galAct σ (A.weight.normRemainder ℓ v) = A.weight.normRemainder ℓ (A.galAct σ v) := by
  rw [WeightData.normRemainder_apply, WeightData.normRemainder_apply, galActOf_smul, map_inv₀,
    map_pow, map_ofNat, map_sub, A.galAct_casimirFactorProd, galActOf_smul,
    WeightData.ringHom_nilpScalar]

/-- **The conjugacy half of `RQ2-3.08-C5`**: `n_⋆ = γ_⋆^{-2}·n` and `n̄_⋆ = γ_⋆^{-2}·n̄` are
conjugate, `σ ∘ n_⋆ = n̄_⋆ ∘ σ` for every `σ ∈ G_E` (`γ_⋆` is rational, hence `σ`-fixed).

@census    none (auxiliary; discharges clause `RQ2-3.08-C5` of `RQ2-3.08`)
@source    def:xstarystar
@clauses   RQ2-3.08-C5
@imports   none
@divergence JUSTIFIED_REFORMULATION (every `σ ∈ G_E`; `n̄ = n`).  The source states the clause
"if `√-1 ∉ E`" for the complex conjugation `c`; here it is stated for **every** `σ ∈ G_E`, which
is `{1, c}` if `√-1 ∉ E` and trivial (`galAct_of_chi_one`) if `√-1 ∈ E`, so the two readings
agree.  `n` and `n̄` are the same operator `WeightData.normRemainder`, so "`c ∘ n = n̄ ∘ c`" reads
`σ ∘ n = n ∘ σ`.  **Proof route** (not the source's): `n` is a polynomial in `C` with rational
coefficients, `C` is `σ`-invariant (`galAct_casimir`, from `cC = C`) and rational scalars are
`σ`-fixed (`galAct_casimirFactorProd`, `ringHom_nilpScalar`).  The source's route — `cX = Yc`,
`cY = Xc` carry `X^{ℓ-1}Y^{ℓ-1}` to `Y^{ℓ-1}X^{ℓ-1}` — is `galAct_normRemainder_of_chi_neg_one`.
-/
theorem galAct_nStar (A : HC ℓ E D) (σ : D.L ≃ₐ[E] D.L) (v : A.carrier) :
    A.galAct σ (((WeightData.gammaStar D.L ℓ ^ 2)⁻¹ • A.weight.normRemainder ℓ) v)
      = ((WeightData.gammaStar D.L ℓ ^ 2)⁻¹ • A.weight.normRemainder ℓ) (A.galAct σ v) := by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, galActOf_smul, A.galAct_normRemainder,
    map_inv₀, map_pow, WeightData.gammaStar, map_natCast]

/-- `c X^r = Y^r c` for `χ_E(σ) = -1`.  @census none -/
theorem galAct_pow_X (A : HC ℓ E D) {σ : D.L ≃ₐ[E] D.L} (hσ : D.chi σ = -1) (r : ℕ)
    (v : A.carrier) : A.galAct σ ((A.weight.X ^ r) v) = (A.weight.Y ^ r) (A.galAct σ v) := by
  obtain ⟨-, hX, -, -⟩ := A.compat_neg hσ
  induction r generalizing v with
  | zero => rfl
  | succ r ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hX]

/-- `c Y^r = X^r c` for `χ_E(σ) = -1`.  @census none -/
theorem galAct_pow_Y (A : HC ℓ E D) {σ : D.L ≃ₐ[E] D.L} (hσ : D.chi σ = -1) (r : ℕ)
    (v : A.carrier) : A.galAct σ ((A.weight.Y ^ r) v) = (A.weight.X ^ r) (A.galAct σ v) := by
  obtain ⟨-, -, hY, -⟩ := A.compat_neg hσ
  induction r generalizing v with
  | zero => rfl
  | succ r ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hY]

/-- **The step of the source's proof of `RQ2-3.06-C6`**: since `cX = Yc` and `cY = Xc`,
conjugation by `c` carries `X^{ℓ-1}Y^{ℓ-1}` to `Y^{ℓ-1}X^{ℓ-1}`:
`σ ∘ (X^r ∘ Y^r) = (Y^r ∘ X^r) ∘ σ` for `χ_E(σ) = -1`.

@census none
-/
theorem galAct_pow_X_mul_pow_Y (A : HC ℓ E D) {σ : D.L ≃ₐ[E] D.L} (hσ : D.chi σ = -1) (r : ℕ)
    (v : A.carrier) :
    A.galAct σ ((A.weight.X ^ r * A.weight.Y ^ r) v)
      = (A.weight.Y ^ r * A.weight.X ^ r) (A.galAct σ v) := by
  rw [Module.End.mul_apply, Module.End.mul_apply, A.galAct_pow_X hσ, A.galAct_pow_Y hσ]

/-- **`c ∘ n = n̄ ∘ c`** (`cor:X_Y_inverses`, clause `RQ2-3.06-C6`), by the source's argument.  For
`χ_E(σ) = -1` (i.e. `σ = c`, `√-1 ∉ E`) and `v ∈ M_{ℓ-1}`: `σ(n v) = n̄(σ v)`, where `n` on
`M_{ℓ-1}` and `n̄` on `M_{-(ℓ-1)}` are the remainders of `eq:XY_inverses_rel` as pinned by
`WeightData.isUnit_pow_X` (`n v = X^{ℓ-1}Y^{ℓ-1}v - γ_⋆²v`, `n̄ w = Y^{ℓ-1}X^{ℓ-1}w - γ_⋆²w`), and
`σ v ∈ M_{-(ℓ-1)}`.  Proof: `σ` carries `X^{ℓ-1}Y^{ℓ-1}` to `Y^{ℓ-1}X^{ℓ-1}`
(`galAct_pow_X_mul_pow_Y`) and fixes the rational scalar `γ_⋆²`.

@census    none (auxiliary; discharges clause `RQ2-3.06-C6` of `RQ2-3.06`)
@source    cor:X_Y_inverses
@clauses   RQ2-3.06-C6
@imports   none
@divergence JUSTIFIED_REFORMULATION (`n̄ = n` as operators on `M`): `n` and `n̄` are the
restrictions of the single operator `WeightData.normRemainder` to `M_{ℓ-1}` and `M_{-(ℓ-1)}`, so
`n̄(σ v)` is `normRemainder (σ v)` with `σ v ∈ M_{-(ℓ-1)}`; the clause's `c` is the `σ` with
`χ_E(σ) = -1`, which exists exactly when `√-1 ∉ E`.  The every-`σ` form is `galAct_normRemainder`.
-/
theorem galAct_normRemainder_of_chi_neg_one (A : HC ℓ E D) (hℓ : 1 ≤ ℓ) {σ : D.L ≃ₐ[E] D.L}
    (hσ : D.chi σ = -1) (v : A.carrier) (hv : v ∈ A.weight.comp ((ℓ : ℤ) - 1)) :
    A.galAct σ v ∈ A.weight.comp (-((ℓ : ℤ) - 1))
      ∧ A.galAct σ (A.weight.normRemainder ℓ v) = A.weight.normRemainder ℓ (A.galAct σ v) := by
  obtain ⟨-, -, -, hXY, hYX⟩ := A.weight.isUnit_pow_X A.gic hℓ
  have hσv : A.galAct σ v ∈ A.weight.comp (-((ℓ : ℤ) - 1)) := (A.compat_neg hσ).1 _ v hv
  refine ⟨hσv, ?_⟩
  have hn : A.weight.normRemainder ℓ v
      = (A.weight.X ^ (ℓ - 1) * A.weight.Y ^ (ℓ - 1)) v
        - WeightData.gammaStar D.L ℓ ^ 2 • v := by
    rw [hXY v hv]; abel
  have hnbar : A.weight.normRemainder ℓ (A.galAct σ v)
      = (A.weight.Y ^ (ℓ - 1) * A.weight.X ^ (ℓ - 1)) (A.galAct σ v)
        - WeightData.gammaStar D.L ℓ ^ 2 • A.galAct σ v := by
    rw [hYX _ hσv]; abel
  rw [hn, hnbar, map_sub, A.galAct_pow_X_mul_pow_Y hσ, galActOf_smul, map_pow,
    WeightData.gammaStar, map_natCast]

end HC

end GalAct


end RationalQuivers.HC
