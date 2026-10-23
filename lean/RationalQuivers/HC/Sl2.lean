import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Sl2
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.Nilpotent.Defs
import RationalQuivers.HC.ImagUnit

/-!
# The classical `sl₂` triple, its Galois symmetry over `L_E`, and the weight bookkeeping

Formalizes the `§3.3`/`§3.4` material of `latex/rational_quivers.tex` that lives on the `𝔰𝔩₂` side
(census `RQ2-3.10` `def:sltwotriple`, generalized from v1 `RQ-3.10`).  The `§3.4` operator
identities (`RQ2-3.04`, `RQ2-3.05`) are in `HC/Normalization.lean`.

## Main definitions / results

* `RationalQuivers.HC.sl2Hm`, `sl2Xm`, `sl2Ym` — the explicit matrices `H`, `X`, `Y`, **as
  renormalized by the author's ruling of 2026-09-10** (`H ↦ −H`, and the explicit `X` and `Y`
  matrices swapped), and `sl2H`, `sl2X`, `sl2Y`, the same three read as elements of
  `𝔤 = 𝔰𝔩₂(ℂ)`.  **These ARE the matrices the paper displays**, at `:1559-1561`, since the author's
  own `latex/` edit landed at **`17fae88`, 2026-09-11**; verified by parsing both sides and
  comparing symbolically, negative-controlled against the pre-edit `.tex` at `ae2e6e2` where all
  three come out DIFFERENT.  Until 2026-09-11 this read: *"**Until the author's `latex/` edit lands
  these are NOT the matrices the paper displays** — the paper still shows the pre-ruling triple at
  `:1559-1561`"* — superseded, kept because a superseded reason is recorded and never deleted
  (`R-PROC-2` item 7).  The renormalization is an automorphism of `𝔰𝔩₂` (inner over `ℂ`), so every
  relation the paper displays at `:1565`, `:1569` and `:1573` holds of the new triple verbatim; see
  the module docstring of `HC/Classical.lean` (v1 `HC/Module.lean`).
* `RationalQuivers.HC.sl2Triple` — census `RQ2-3.10`: they are an `sl₂` triple, i.e.
  `[H,X] = 2X`, `[H,Y] = -2Y`, `[X,Y] = H`.
* `RationalQuivers.HC.conjG` — the action of `c ∈ Gal(ℚ[√-1]/ℚ)` on matrix entries, and
  `conj_triple` (`cH = -H`, `cX = Y`, `cY = X`), `rationalForm_eq_sl2Q` (the resulting `ℚ`-form is
  `𝔰𝔩_{2,ℚ}`).
* `RationalQuivers.HC.WeightData` — the `§3.3` bookkeeping this stage runs on: an `E`-vector space
  with its `SO(2)`-isotypic decomposition `M_n = M[χ_n]` and the action of the triple.
* `RationalQuivers.HC.ImagUnit.sl2H`, `sl2X`, `sl2Y`, `sl2TripleOver`, `galSl_conj_triple`,
  `rationalForm_eq_range`, `triple_mem_range_of_sqrt` — the triple over `L_E` for `D : ImagUnit E`
  (`E` of characteristic `0`): an `sl₂` triple in `𝔤_{L_E}`, `σH = χ_E(σ)H`, `cX = Y`, `cY = X`, the
  `G_E`-fixed part of `𝔤_{L_E}` is `𝔰𝔩_{2,E}`, and `H, X, Y ∈ 𝔤_E` if `√-1 ∈ E` (clauses
  `RQ2-3.10-C3`…`C6`); `ImagUnit.qi` is `ℚ[√-1]/ℚ` with `L := Qi`.
* `RationalQuivers.HC.WeightData.casimir` — `C = H² - 2H + 4XY + 1`.

## Implementation notes

**Why our own `WeightData` rather than mathlib's weight spaces.**  mathlib's
`LieModule.weightSpace` is indexed by the duals of a *Cartan subalgebra* and developed for
finite-dimensional modules; the paper's `M_n = M[χ_n]` are the isotypic components for the
characters `χ_n` of the compact torus `SO(2,ℝ)` on a module that is in general infinite-dimensional
(admissible, not finite-dimensional).  Ledger row `MD-S7-01`.

**`H` acts by `n` on `M_n`.**  This is forced by the source, not a convention we chose: the proof of
`prop:XY_C_relation` uses `4XY = C - H² + 2H - 1 = C - p²` on `M_{p+1}`, which pins the scalar by
which `H` acts on `M_{p+1}` to `p+1`.  `X` therefore raises the index by `2` and `Y` lowers it by
`2`.

**Products of operators.**  The right-hand side of `eq:XYm_via_C` is a product over `j = 0 … m-1`
of pairwise commuting operators, so its value does not depend on the order; `casimirFactorProd`
nevertheless fixes one order (ascending `j`, via `List.prod`) so that the statement is a single
term rather than a `Finset.noncommProd` carrying a commutation proof.

**The `ℚ`-form without S0.**  `rationalForm` is built by hand from `IntermediateField.adjoin ℚ {I}`
and the entrywise conjugation, *not* from `RationalQuivers/Descent/`: `workflow/PLAN.md` §2's stage
DAG has S6 as S7's only predecessor, so `rqaudit deps --no-forward` forbids importing S0's descent
machinery here.  See `workflow/stages/S7/DESIGN-NOTES.md` §3.
-/

universe u v

namespace RationalQuivers.HC

open Matrix Complex LieAlgebra.SpecialLinear

/-! ## §3.3 — the classical triple (census `RQ2-3.10`) -/

/-- `𝔤 = 𝔰𝔩_{2,ℂ}`, mathlib's special linear Lie algebra of trace-zero `2×2` complex matrices.

@census none
-/
abbrev gC := sl (Fin 2) ℂ

/-- `H = !![0, i; -i, 0]`, the first member of the classical triple, **renormalized** by the
author's ruling of 2026-09-10 (`H ↦ −H`, with `X` and `Y` swapped below) — and **this is what the
source displays**, at `:1559`, since the author's `latex/` edit landed at `17fae88` (2026-09-11).
Until 2026-09-11 this docstring read: *"the source displays `!![0, -i; i, 0]` and the ruling negates
it"* — true when written, superseded and not deleted (`R-PROC-2` item 7).  See the module docstring
of `HC/Classical.lean` (v1 `HC/Module.lean`).

@census none
-/
noncomputable def sl2Hm : Matrix (Fin 2) (Fin 2) ℂ := !![0, I; -I, 0]

/-- `X = ½ · !![1, -i; -i, -1]` — **the matrix the source displays as `X`**, at `:1560`, since the
author's `latex/` edit landed at `17fae88` (2026-09-11).  It carries this name by the ruling of
2026-09-10, which **swapped** the two pre-ruling matrices.  Until 2026-09-11 this docstring read:
*"the matrix the source displays as `Y`, **swapped** into `X`"* — true when written, superseded and
not deleted (`R-PROC-2` item 7).

@census none
-/
noncomputable def sl2Xm : Matrix (Fin 2) (Fin 2) ℂ := !![2⁻¹, -(2⁻¹ * I); -(2⁻¹ * I), -2⁻¹]

/-- `Y = ½ · !![1, i; i, -1]` — **the matrix the source displays as `Y`**, at `:1561`, since the
author's `latex/` edit landed at `17fae88` (2026-09-11).  It carries this name by the ruling of
2026-09-10, which **swapped** the two pre-ruling matrices.  Until 2026-09-11 this docstring read:
*"the matrix the source displays as `X`, **swapped** into `Y`"* — true when written, superseded and
not deleted (`R-PROC-2` item 7).

@census none
-/
noncomputable def sl2Ym : Matrix (Fin 2) (Fin 2) ℂ := !![2⁻¹, 2⁻¹ * I; 2⁻¹ * I, -2⁻¹]

theorem sl2Hm_mem : sl2Hm ∈ gC := by
  show Matrix.trace sl2Hm = 0
  simp [sl2Hm, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem sl2Xm_mem : sl2Xm ∈ gC := by
  show Matrix.trace sl2Xm = 0
  simp [sl2Xm, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem sl2Ym_mem : sl2Ym ∈ gC := by
  show Matrix.trace sl2Ym = 0
  simp [sl2Ym, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- `H` as an element of `𝔤`.

@census none
-/
noncomputable def sl2H : gC := ⟨sl2Hm, sl2Hm_mem⟩

/-- `X` as an element of `𝔤`.

@census none
-/
noncomputable def sl2X : gC := ⟨sl2Xm, sl2Xm_mem⟩

/-- `Y` as an element of `𝔤`.

@census none
-/
noncomputable def sl2Y : gC := ⟨sl2Ym, sl2Ym_mem⟩

/-- **The classical triple** (`§3.3`, `def:sltwotriple`, census `RQ2-3.10`).  The explicit matrices
`H`, `X`, `Y` satisfy the usual `𝔰𝔩₂` relations `[H,X] = 2X`, `[H,Y] = -2Y`, `[X,Y] = H` —
mathlib's
`IsSl2Triple h e f` is exactly those three relations (plus `h ≠ 0`), with `h = H`, `e = X`,
`f = Y`, so the paper's display is used in mathlib's own spelling rather than restated
(`CONVENTIONS.md` §6, ladder step 1).

The remaining clauses of this row are discharged next to it: `sl2_isBasis` (C1, the triple is a
`ℂ`-basis of `𝔤`), `conj_triple` (C3, the Galois symmetry), `rationalForm_eq_sl2Q` (C4, the
resulting `ℚ`-form is `𝔰𝔩_{2,ℚ}`).  The row is generalized to a field `E` of
characteristic `0` with `i` read as `√-1 ∈ L_E` (`def:sqrtminusone`); the `L_E`-clauses are
discharged in namespace `ImagUnit` below: `ImagUnit.sl2TripleOver` (`H1`, `C5`: the triple lies in
`𝔤_{L_E}` and satisfies the relations), `ImagUnit.galSl_conj_triple` (`C3`),
`ImagUnit.rationalForm_eq_range` (`C4`), `ImagUnit.triple_mem_range_of_sqrt` (`C6`).  This
declaration states `C2` for `𝔤 = 𝔰𝔩_{2,ℂ}`, the row's `g`.

@census    RQ2-3.10
@source    def:sltwotriple
@clauses   RQ2-3.10-H1, RQ2-3.10-C2
@imports   none
@divergence none.  **The `JUSTIFIED_REFORMULATION` this row carried from 2026-09-10 to 2026-09-11
is RETIRED, not reworded.**  The author's own `latex/` edit landed at **`17fae88`, 2026-09-11**, and
`latex/rational_quivers.tex:1559-1561` now displays exactly the three matrices this file defines, so
there is nothing left to disclose: the `lean/`-against-`latex/` disagreement the field existed to
state no longer exists.

**`sl2Triple`'s STATEMENT is unchanged by this retirement.**  Only the disclosure retires.  The
theorem, its signature, `sl2H`/`sl2X`/`sl2Y` and `sl2Hm`/`sl2Xm`/`sl2Ym` are byte-identical to what
they were before; this edit is a docstring and nothing else, measured as such (`lake build` 0,
`lake build RQAudit` 0, `decl-regression --stage S7 --baseline 24057f8` still 7 `CHANGED`, 0
`MISSING`, 0 `ADDED` — not 8).

**The retired disclosure, kept because a superseded reason is recorded and never deleted
(`R-PROC-2` item 7).**  It read: *`JUSTIFIED_REFORMULATION` (the three EXPLICIT matrices, by the
paper author's ruling of 2026-09-10 — disclosed; **expected to RETIRE when the author's own `latex/`
edit lands**, obligation `O-S7-SL2-1`, author item `AN-34`)*, on the ground that the paper then
displayed `H = !![0, -i; i, 0]`, `X = ½ · !![1, i; i, -1]`, `Y = ½ · !![1, -i; -i, -1]` at
`:1559-1561` while this file stated `sl2Hm = !![0, i; -i, 0]`, `sl2Xm = ½ · !![1, -i; -i, -1]`,
`sl2Ym = ½ · !![1, i; i, -1]` — `H ↦ −H` with the displayed `X` and `Y` **swapped**, `χ_n` left as
printed.  **Why that was so** is unchanged and is not repeated here: the source's §3.3 display was
inconsistent by a sign with its own §5.1/§5.3 arithmetic, the author ruled on 2026-09-10 that the
repair is made in `H`, and that ruling **supersedes** coordinator ruling `R-S7-6` of 2026-09-02.  The
full reasoning is recorded at the `HarishChandraModule` docstring of `HC/Classical.lean` (v1
`HC/Module.lean`) and in
`workflow/stages/S7/FREEZE.md`'s `R-PROC-4` amendment entry of 2026-09-10.

**What retires it is a measurement, not the commit message.**  The two triples were compared
**symbolically**, parsing both sides rather than retyping either — the three `pmatrix` displays at
`.tex:1559-1561` (with their `\frac{1}{2}` prefixes) against the right-hand sides of the three
**declarations** `sl2Hm`, `sl2Xm` and `sl2Ym` above — and `tex − lean` was the zero matrix in all
three cases.  The same parsed `lean` triple satisfies `[H,X] = 2X`, `[H,Y] = −2Y`, `[X,Y] = H` with
zero residual, and each member is trace-zero.  The comparator was **negative-controlled** against
the pre-edit `.tex` at `ae2e6e2`, where it reports all three matrices `DIFFERENT` and exits 1; a
green that cannot go red would not be evidence.  Recorded in `workflow/stages/S7/FREEZE.md`'s
`R-PROC-4` amendment entries of 2026-09-11.

**Why this citation names DECLARATIONS and not line numbers**, since the sentence above is its own
worked example.  It used to read *"the three `!![…]` literals at `HC/Sl2.lean:83`/`:90`/`:97`"*.
Those numbers were **correct at the commit that wrote them** — at `e766054` the three `def`s did
stand at `83`, `90` and `97`, re-derived by `git show` — and they were falsified twice over by
**later rounds of the same prose sequence editing this same file**: to `86`/`96`/`106` at `55504b5`,
then to `91`/`101`/`111` at `ae53140`, each time leaving the citation pointing into a docstring.
Re-deriving after one's own edit does not help, because what falsifies the number is somebody else's
later edit.  A declaration name survives all of them.  Recorded in
`workflow/stages/S7/FREEZE.md`'s round-5 entry of 2026-09-11.

**What this retirement does NOT claim.**  It does not say the erratum never existed — the tree's
history holds it, and `AN-34` is closed by the author's edit, not erased by it.  It does not touch
obligation `O-S7-SL2-1`, whose subject is a different thing: `workflow/census/ATTESTATION.md` §11's
`R-13` source-provenance row for that same edit, owned by the census adjudicator and dischargeable
only behind F1.  That obligation was **DISCHARGED on 2026-09-11**, at `6e6e76d`, by the census
adjudicator behind F1 — see `workflow/ledger/OBLIGATIONS.md`'s `O-S7-SL2-1 — DISCHARGED 2026-09-11`
entry.  Until 2026-09-11 this passage read: *"That obligation's blocking condition is now **met**;
the obligation itself is still **open**"* — **true when written** and stale twenty minutes later:
it was written at `e766054` (11:58) and the discharge landed at `6e6e76d` (12:18), before any later
prose round opened this file.  The three commits that edited this file afterwards
(`55504b5`, `4341e83`, `ae53140`) all left the sentence standing.  Superseded and not deleted
(`R-PROC-2` item 7).
-/
theorem sl2Triple : IsSl2Triple sl2H sl2X sl2Y := by
  constructor
  · intro h
    have h2 : sl2Hm 0 1 = (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 := by
      rw [show sl2Hm = ((sl2H : gC) : Matrix (Fin 2) (Fin 2) ℂ) from rfl, h]; rfl
    simp [sl2Hm] at h2
  · apply Subtype.ext
    rw [sl_bracket]
    show sl2Xm * sl2Ym - sl2Ym * sl2Xm = sl2Hm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2Xm, sl2Ym, sl2Hm] <;> ring_nf
  · rw [two_nsmul]
    apply Subtype.ext
    rw [sl_bracket]
    show sl2Hm * sl2Xm - sl2Xm * sl2Hm = sl2Xm + sl2Xm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2Xm, sl2Hm] <;> ring_nf <;>
      simp [Complex.I_sq]
  · rw [two_nsmul]
    apply Subtype.ext
    rw [sl_bracket]
    show sl2Hm * sl2Ym - sl2Ym * sl2Hm = -(sl2Ym + sl2Ym)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2Ym, sl2Hm] <;> ring_nf <;>
      simp [Complex.I_sq]

/-- The triple is `ℂ`-linearly independent: reading off the `(0,0)`, `(0,1)` and `(1,0)` entries of
`aH + bX + cY = 0` gives `b + c = 0`, `i(c - b) = 0` and then `ai = 0`.  (`i(b - c) = 0` until the
author's ruling of 2026-09-10 swapped `X` and `Y`; the conclusion is unchanged.)

@census none
-/
theorem sl2_linearIndependent : LinearIndependent ℂ ![sl2H, sl2X, sl2Y] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 : g 0 • sl2Hm + g 1 • sl2Xm + g 2 • sl2Ym = 0 := by
    have h := congrArg (fun x : gC => (x : Matrix (Fin 2) (Fin 2) ℂ)) hg
    simpa [Fin.sum_univ_three, sl2H, sl2X, sl2Y] using h
  have e00 := congrFun (congrFun h0 0) 0
  have e01 := congrFun (congrFun h0 0) 1
  have e10 := congrFun (congrFun h0 1) 0
  simp [sl2Hm, sl2Xm, sl2Ym] at e00 e01 e10
  have hd : I * (g 1 - g 2) = 0 := by linear_combination -(e01 + e10)
  have h12 : g 1 - g 2 = 0 := by
    rcases mul_eq_zero.mp hd with h | h
    · exact absurd h Complex.I_ne_zero
    · exact h
  have hs : g 1 + g 2 = 0 := by linear_combination 2 * e00
  have hg1 : g 1 = 0 := by linear_combination (h12 + hs) / 2
  have hg2 : g 2 = 0 := by linear_combination (hs - h12) / 2
  have hg0 : g 0 * I = 0 := by linear_combination -e10 - (2⁻¹ * I) * hg1 + (2⁻¹ * I) * hg2
  have hg0' : g 0 = 0 := by
    rcases mul_eq_zero.mp hg0 with h | h
    · exact h
    · exact absurd h Complex.I_ne_zero
  intro i
  fin_cases i <;> assumption


/-- The triple spans `𝔤 = 𝔰𝔩_{2,ℂ}` over `ℂ`: the trace-zero matrix `!![a,b;c,-a]` is
`(i(c-b)/2)·H + (a + i(b+c)/2)·X + (a - i(b+c)/2)·Y`.  (Before the author's ruling of 2026-09-10
this read `(i(b-c)/2)·H + (a - i(b+c)/2)·X + (a + i(b+c)/2)·Y`: the `H`-coefficient is negated
because `H` is, and the `X`/`Y` coefficients are interchanged because `X` and `Y` are.  The
STATEMENT — that the triple spans — does not move.)

@census none
-/
theorem sl2_span_top : ⊤ ≤ Submodule.span ℂ (Set.range ![sl2H, sl2X, sl2Y]) := by
  rintro x -
  obtain ⟨A, hA⟩ := x
  rw [Submodule.mem_span_range_iff_exists_fun]
  have htr : Matrix.trace A = 0 := hA
  rw [Matrix.trace_fin_two] at htr
  refine ⟨![I * (A 1 0 - A 0 1) / 2, A 0 0 + I * (A 0 1 + A 1 0) / 2,
    A 0 0 - I * (A 0 1 + A 1 0) / 2], ?_⟩
  apply Subtype.ext
  ext i j
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  fin_cases i <;> fin_cases j
  · simp [sl2H, sl2X, sl2Y, sl2Hm, sl2Xm, sl2Ym]; ring
  · simp [sl2H, sl2X, sl2Y, sl2Hm, sl2Xm, sl2Ym]
    linear_combination (-(A 0 1)) * Complex.I_sq
  · simp [sl2H, sl2X, sl2Y, sl2Hm, sl2Xm, sl2Ym]
    linear_combination (-(A 1 0)) * Complex.I_sq
  · simp [sl2H, sl2X, sl2Y, sl2Hm, sl2Xm, sl2Ym]
    linear_combination -htr

/-- `RQ2-3.10-C1`: `H`, `X`, `Y` are a `ℂ`-basis of `𝔤 = 𝔰𝔩_{2,ℂ}`.

@census    none (auxiliary; discharges clause `RQ2-3.10-C1` of `RQ2-3.10`)
@source    def:sltwotriple
@clauses   RQ2-3.10-C1
@imports   none
@divergence none
-/
theorem sl2_isBasis : ∃ b : Module.Basis (Fin 3) ℂ gC, ⇑b = ![sl2H, sl2X, sl2Y] :=
  ⟨Module.Basis.mk sl2_linearIndependent sl2_span_top, Module.Basis.coe_mk _ _⟩

/-! ### The Galois action `c ∈ Gal(ℚ[√-1]/ℚ)` -/

/-- `c` acting on the entries of a complex matrix.

@census none
-/
def conjMat (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := A.map (starRingEnd ℂ)

@[simp] theorem conjMat_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    conjMat A i j = (starRingEnd ℂ) (A i j) := rfl

theorem conjMat_mem {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ gC) : conjMat A ∈ gC := by
  have h : Matrix.trace A = 0 := hA
  have : Matrix.trace (conjMat A) = (starRingEnd ℂ) (Matrix.trace A) := by
    simp [Matrix.trace, Matrix.diag, conjMat, Fin.sum_univ_two]
  show Matrix.trace (conjMat A) = 0
  rw [this, h, map_zero]

/-- `c` acting on `𝔤 = 𝔰𝔩_{2,ℂ}`.  It is `ℚ`-linear but only `ℂ`-*semi*linear, which is why it is
carried as a bare function on `𝔤` here and as a `ℚ`-submodule condition in `rationalForm`.

@census none
-/
def conjG (x : gC) : gC := ⟨conjMat x.1, conjMat_mem x.2⟩

/-- `RQ2-3.10-C3` at `E = ℚ` (`L_E = ℚ[i] ⊆ ℂ`): the Galois symmetry `cH = -H`, `cX = Y`, `cY = X`
that generates the whole rational theory of `§3`–`§5`, `c` acting on `𝔤 = 𝔰𝔩_{2,ℂ}` as complex
conjugation of entries.  The general-`E` form is `ImagUnit.galSl_conj_triple`.

@census    none (auxiliary; discharges clause `RQ2-3.10-C3` of `RQ2-3.10`)
@source    def:sltwotriple
@clauses   RQ2-3.10-C3
@imports   none
@divergence none
-/
theorem conj_triple : conjG sl2H = -sl2H ∧ conjG sl2X = sl2Y ∧ conjG sl2Y = sl2X := by
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩ <;>
    (show conjMat _ = _
     ext i j
     fin_cases i <;> fin_cases j <;>
       simp [conjMat, sl2H, sl2X, sl2Y, sl2Hm, sl2Xm, sl2Ym, Complex.ext_iff])

/-! ### The `ℚ`-rational form -/

/-- `ℚ[√-1] ⊆ ℂ`.

@census none
-/
noncomputable abbrev Qi : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {Complex.I}

/-- Complex conjugation as a `ℚ`-algebra automorphism of `ℂ`.

@census none
-/
noncomputable def conjQ : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ

theorem conjQ_I : conjQ Complex.I = -Complex.I := by simp [conjQ]

theorem Qi_map : Qi.map (conjQ : ℂ ≃ₐ[ℚ] ℂ).toAlgHom = Qi := by
  have himg : (⇑(conjQ : ℂ ≃ₐ[ℚ] ℂ).toAlgHom) '' {Complex.I} = {-Complex.I} := by
    rw [Set.image_singleton]; exact congrArg _ conjQ_I
  rw [IntermediateField.adjoin_map, himg]
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact neg_mem (IntermediateField.subset_adjoin ℚ _ rfl)
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have h : -Complex.I ∈ IntermediateField.adjoin ℚ ({-Complex.I} : Set ℂ) :=
      IntermediateField.subset_adjoin ℚ _ rfl
    simpa using neg_mem h

/-- The non-trivial element `c ∈ Gal(ℚ[√-1]/ℚ)`, obtained by restricting complex conjugation.
Used by `§3.4`'s standing setup (`RQ2-3.06-Hs1`) as the semilinearity datum of the Galois action on
`M_{ℚ[√-1]}`.

@census none
-/
noncomputable def galConj : Qi ≃ₐ[ℚ] Qi :=
  (IntermediateField.intermediateFieldMap conjQ Qi).trans (IntermediateField.equivOfEq Qi_map)

/-- `𝔤_{ℚ[√-1]}`: the `ℚ[√-1]`-span of the triple inside the complex `2×2` matrices, viewed as a
`ℚ`-subspace so that it can be intersected with the `c`-fixed points.

@census none
-/
noncomputable def gQi : Submodule ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Submodule.restrictScalars ℚ (Submodule.span Qi {sl2Hm, sl2Xm, sl2Ym})

/-- The `c`-fixed complex matrices, i.e. the real ones — a `ℚ`-subspace.

@census none
-/
def conjFixed : Submodule ℚ (Matrix (Fin 2) (Fin 2) ℂ) where
  carrier := {A | conjMat A = A}
  zero_mem' := by ext i j; simp
  add_mem' := by
    intro a b ha hb
    have ha' : ∀ i j, (starRingEnd ℂ) (a i j) = a i j := fun i j => congrFun (congrFun ha i) j
    have hb' : ∀ i j, (starRingEnd ℂ) (b i j) = b i j := fun i j => congrFun (congrFun hb i) j
    ext i j
    show (starRingEnd ℂ) (a i j + b i j) = a i j + b i j
    rw [map_add, ha', hb']
  smul_mem' := by
    intro q a ha
    have ha' : ∀ i j, (starRingEnd ℂ) (a i j) = a i j := fun i j => congrFun (congrFun ha i) j
    ext i j
    show (starRingEnd ℂ) ((q • a) i j) = (q • a) i j
    simp only [Matrix.smul_apply, Rat.smul_def, map_mul, map_ratCast, ha']

/-- `𝔤_ℚ`: the `ℚ`-rational form of `𝔤` cut out by the Galois action — the `c`-fixed vectors of the
`ℚ[√-1]`-form `𝔤_{ℚ[√-1]}`.

@census none
-/
noncomputable def rationalForm : Submodule ℚ (Matrix (Fin 2) (Fin 2) ℂ) := gQi ⊓ conjFixed

/-- `𝔰𝔩_{2,ℚ}`, the trace-zero rational matrices, pushed into the complex `2×2` matrices.

@census none
-/
noncomputable def sl2QIn : Submodule ℚ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Submodule.map (LinearMap.mapMatrix (Algebra.linearMap ℚ ℂ))
    (LinearMap.ker (Matrix.traceLinearMap (Fin 2) ℚ ℚ))

/-! ### `ℚ[√-1] = ℚ + ℚ·i`, and the `ℚ`-points of the form -/

/-- `ℚ + ℚ·i` as an intermediate field of `ℂ/ℚ`. -/
noncomputable def QiModel : IntermediateField ℚ ℂ where
  carrier := {z : ℂ | ∃ p q : ℚ, z = (p : ℂ) + (q : ℂ) * I}
  mul_mem' := by
    rintro _ _ ⟨p, q, rfl⟩ ⟨r, s, rfl⟩
    refine ⟨p * r - q * s, p * s + q * r, ?_⟩
    push_cast
    linear_combination ((q : ℂ) * (s : ℂ)) * Complex.I_sq
  add_mem' := by
    rintro _ _ ⟨p, q, rfl⟩ ⟨r, s, rfl⟩
    exact ⟨p + r, q + s, by push_cast; ring⟩
  algebraMap_mem' r := ⟨r, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨p, q, rfl⟩
    by_cases h : (p : ℂ) + (q : ℂ) * I = 0
    · exact ⟨0, 0, by rw [h]; simp⟩
    · have hpq : ¬ (p = 0 ∧ q = 0) := by
        rintro ⟨rfl, rfl⟩
        simp at h
      have hn : (p ^ 2 + q ^ 2 : ℚ) ≠ 0 := by
        intro hz
        refine hpq ⟨?_, ?_⟩ <;> nlinarith [sq_nonneg p, sq_nonneg q]
      refine ⟨p / (p ^ 2 + q ^ 2), -q / (p ^ 2 + q ^ 2), ?_⟩
      have hnC : ((p : ℂ) ^ 2 + (q : ℂ) ^ 2) ≠ 0 := by
        have : ((p ^ 2 + q ^ 2 : ℚ) : ℂ) ≠ 0 := by
          exact_mod_cast Rat.cast_ne_zero.mpr hn
        push_cast at this
        exact this
      refine inv_eq_of_mul_eq_one_right ?_
      push_cast
      field_simp
      linear_combination (-(q : ℂ) ^ 2) * Complex.I_sq

theorem mem_QiModel_iff (z : ℂ) : z ∈ QiModel ↔ ∃ p q : ℚ, z = (p : ℂ) + (q : ℂ) * I := Iff.rfl

theorem mem_Qi_iff (z : ℂ) : z ∈ Qi ↔ ∃ p q : ℚ, z = (p : ℂ) + (q : ℂ) * I := by
  constructor
  · intro hz
    have hle : Qi ≤ QiModel := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ rfl
      exact ⟨0, 1, by simp⟩
    exact hle hz
  · rintro ⟨p, q, rfl⟩
    have hI : Complex.I ∈ Qi := IntermediateField.subset_adjoin ℚ _ rfl
    have hp : ((p : ℂ)) ∈ Qi := Qi.algebraMap_mem p
    have hq : ((q : ℂ)) ∈ Qi := Qi.algebraMap_mem q
    exact add_mem hp (mul_mem hq hI)

theorem rat_of_mem_Qi_of_conj {z : ℂ} (hz : z ∈ Qi) (hc : (starRingEnd ℂ) z = z) :
    ∃ r : ℚ, z = (r : ℂ) := by
  obtain ⟨p, q, rfl⟩ := (mem_Qi_iff z).mp hz
  refine ⟨p, ?_⟩
  have h1 := congrArg Complex.im hc
  simp at h1
  have hq : q = 0 := by
    have : (q : ℝ) = 0 := by linarith
    exact_mod_cast this
  rw [hq]
  simp

theorem qi_smul_matrix (c : Qi) (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (c • M) i j = (c : ℂ) * M i j := by
  rw [Matrix.smul_apply, Algebra.smul_def]
  rfl

noncomputable def qiTraceZero : Submodule Qi (Matrix (Fin 2) (Fin 2) ℂ) where
  carrier := {A | (∀ i j, A i j ∈ Qi) ∧ Matrix.trace A = 0}
  zero_mem' := ⟨fun _ _ => zero_mem _, by simp⟩
  add_mem' := fun {a b} ha hb =>
    ⟨fun i j => add_mem (ha.1 i j) (hb.1 i j), by
      rw [Matrix.trace_add, ha.2, hb.2, add_zero]⟩
  smul_mem' := fun c A hA =>
    ⟨fun i j => by
        rw [Matrix.smul_apply, Algebra.smul_def]
        exact mul_mem c.2 (hA.1 i j), by
      rw [Matrix.trace_smul, hA.2, smul_zero]⟩

theorem span_le_qiTraceZero :
    Submodule.span Qi {sl2Hm, sl2Xm, sl2Ym} ≤ qiTraceZero := by
  rw [Submodule.span_le]
  have hI : Complex.I ∈ Qi := IntermediateField.subset_adjoin ℚ _ rfl
  have hhalf : (2⁻¹ : ℂ) ∈ Qi := by
    have h := Qi.algebraMap_mem (2⁻¹ : ℚ)
    rwa [show (algebraMap ℚ ℂ) (2⁻¹ : ℚ) = (2⁻¹ : ℂ) by norm_num] at h
  have hmem : ∀ z : ℂ, z ∈ Qi → ∀ w : ℂ, w ∈ Qi → z * w ∈ Qi := fun _ hz _ hw => mul_mem hz hw
  rintro A (rfl | rfl | rfl) <;>
    refine ⟨?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [sl2Hm] <;>
      first | exact zero_mem _ | exact hI
  · exact sl2Hm_mem
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [sl2Xm] <;>
      first | exact hhalf | exact neg_mem hhalf | exact mul_mem hhalf hI
  · exact sl2Xm_mem
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [sl2Ym] <;>
      first | exact hhalf | exact neg_mem hhalf | exact mul_mem hhalf hI
  · exact sl2Ym_mem

/-- `RQ2-3.10-C4` at `E = ℚ` ("for `E = ℚ` this is `𝔰𝔩_{2,ℚ}`"): the `ℚ`-rational form of `𝔤`
determined by the Galois action `c` **agrees with** `𝔰𝔩_{2,ℚ}`.  The general-`E` form is
`ImagUnit.rationalForm_eq_range`.

@census    none (auxiliary; discharges clause `RQ2-3.10-C4` of `RQ2-3.10`)
@source    def:sltwotriple
@clauses   RQ2-3.10-C4
@imports   none
@divergence none
-/
theorem rationalForm_eq_sl2Q : rationalForm = sl2QIn := by
  have hI : Complex.I ∈ Qi := IntermediateField.subset_adjoin ℚ _ rfl
  apply le_antisymm
  · rintro A ⟨hA1, hA2⟩
    have hA1' : A ∈ Submodule.span Qi {sl2Hm, sl2Xm, sl2Ym} := hA1
    obtain ⟨hent, htr⟩ := span_le_qiTraceZero hA1'
    have hconj : ∀ i j, (starRingEnd ℂ) (A i j) = A i j := by
      intro i j
      have : conjMat A = A := hA2
      exact congrFun (congrFun this i) j
    choose R hR using fun (i : Fin 2) (j : Fin 2) => rat_of_mem_Qi_of_conj (hent i j) (hconj i j)
    refine ⟨Matrix.of R, ?_, ?_⟩
    · show Matrix.trace (Matrix.of R) = 0
      rw [Matrix.trace_fin_two] at htr ⊢
      have h0 := hR 0 0
      have h1 := hR 1 1
      rw [h0, h1] at htr
      have : ((R 0 0 + R 1 1 : ℚ) : ℂ) = ((0 : ℚ) : ℂ) := by push_cast; simpa using htr
      exact_mod_cast this
    · ext i j
      show algebraMap ℚ ℂ (R i j) = A i j
      rw [hR i j]
      simp
  · rintro A ⟨R, hR, rfl⟩
    have hRtr : Matrix.trace R = 0 := hR
    constructor
    · show _ ∈ Submodule.span Qi {sl2Hm, sl2Xm, sl2Ym}
      have hset : ({sl2Hm, sl2Xm, sl2Ym} : Set (Matrix (Fin 2) (Fin 2) ℂ))
          = Set.range ![sl2Hm, sl2Xm, sl2Ym] := by
        ext z
        constructor
        · rintro (rfl | rfl | rfl)
          exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
        · rintro ⟨i, rfl⟩
          fin_cases i <;> simp
      rw [hset, Submodule.mem_span_range_iff_exists_fun]
      have hq : ∀ r : ℚ, ((r : ℂ)) ∈ Qi := fun r => Qi.algebraMap_mem r
      have hqI : ∀ r : ℚ, ((r : ℂ)) * Complex.I ∈ Qi := fun r => mul_mem (hq r) hI
      refine ⟨![⟨((((R 1 0 - R 0 1) / 2 : ℚ) : ℂ)) * Complex.I, hqI _⟩,
        ⟨(((R 0 0 : ℚ) : ℂ)) + (((((R 0 1 + R 1 0) / 2 : ℚ)) : ℂ)) * Complex.I,
          add_mem (hq _) (hqI _)⟩,
        ⟨(((R 0 0 : ℚ) : ℂ)) + ((((-(R 0 1 + R 1 0) / 2 : ℚ)) : ℂ)) * Complex.I,
          add_mem (hq _) (hqI _)⟩], ?_⟩
      have htr2 : (R 1 1 : ℚ) = -R 0 0 := by
        rw [Matrix.trace_fin_two] at hRtr; linarith
      ext i j
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.add_apply, qi_smul_matrix]
      fin_cases i <;> fin_cases j <;>
        simp [sl2Hm, sl2Xm, sl2Ym, htr2]
      all_goals ring_nf
      all_goals rw [Complex.I_sq]
      all_goals ring
    · show conjMat _ = _
      ext i j
      simp

/-! ## The triple over `L_E` (census `RQ2-3.10`, `def:sltwotriple`, generalized)

For a field `E` of characteristic `0` and a datum `D : ImagUnit E` (`L_E = E[√-1]`,
`def:sqrtminusone`, `HC/ImagUnit.lean`), the matrices `H`, `X`, `Y` above are read with the entry
`i` as `D.i = √-1 ∈ L_E` (`ImagUnit.sl2Hm`, …; the same literals as `sl2Hm`, … with
`Complex.I ↦ D.i`).  `σ ∈ G_E` acts on matrix entries (`ImagUnit.galSl`): `σH = χ_E(σ)H`, and `c`
(`χ_E = -1`) swaps `X` and `Y`; the `G_E`-fixed vectors of `𝔤_{L_E} = 𝔰𝔩_{2,L_E}` are exactly
`𝔰𝔩_{2,E}` (`ImagUnit.rationalForm_eq_range`, by `IsGalois.mem_range_algebraMap_iff_fixed`); if
`√-1 ∈ E`, `H`, `X`, `Y` already lie in `𝔤_E`. -/

/-- **`ℚ[√-1]/ℚ`** as an `ImagUnit ℚ`: `L := HC.Qi = ℚ(i) ⊆ ℂ`, `i := Complex.I`.

@census none (helper)
-/
noncomputable def ImagUnit.qi : ImagUnit ℚ where
  L := (Qi : Type)
  i := ⟨Complex.I, IntermediateField.subset_adjoin ℚ _ rfl⟩
  i_mul_i := by apply Subtype.ext; simp
  adjoin_eq_top := by
    rw [eq_top_iff]
    rintro ⟨z, hz⟩ -
    obtain ⟨p, q, rfl⟩ := (mem_Qi_iff z).mp hz
    have hI : (⟨Complex.I, IntermediateField.subset_adjoin ℚ _ rfl⟩ : Qi) ∈
        Algebra.adjoin ℚ ({⟨Complex.I, IntermediateField.subset_adjoin ℚ _ rfl⟩} : Set Qi) :=
      Algebra.subset_adjoin rfl
    have : (⟨(p : ℂ) + (q : ℂ) * Complex.I, hz⟩ : Qi) = algebraMap ℚ Qi p
        + algebraMap ℚ Qi q * ⟨Complex.I, IntermediateField.subset_adjoin ℚ _ rfl⟩ := by
      apply Subtype.ext; simp
    rw [this]
    exact add_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (Subalgebra.algebraMap_mem _ _) hI)

theorem ImagUnit.qi_i : (((show Qi from ImagUnit.qi.i) : Qi) : ℂ) = Complex.I := rfl

namespace ImagUnit

variable {E : Type} [Field E] (D : ImagUnit E)

/-- `H = !![0, i; -i, 0]` over `L_E`, `i = √-1` (`sl2Hm` with `Complex.I ↦ D.i`).

@census none
-/
noncomputable def sl2Hm : Matrix (Fin 2) (Fin 2) D.L := !![0, D.i; -D.i, 0]

/-- `X = ½ · !![1, -i; -i, -1]` over `L_E` (`sl2Xm` with `Complex.I ↦ D.i`).

@census none
-/
noncomputable def sl2Xm : Matrix (Fin 2) (Fin 2) D.L :=
  !![2⁻¹, -(2⁻¹ * D.i); -(2⁻¹ * D.i), -2⁻¹]

/-- `Y = ½ · !![1, i; i, -1]` over `L_E` (`sl2Ym` with `Complex.I ↦ D.i`).

@census none
-/
noncomputable def sl2Ym : Matrix (Fin 2) (Fin 2) D.L := !![2⁻¹, 2⁻¹ * D.i; 2⁻¹ * D.i, -2⁻¹]

theorem sl2Hm_mem : D.sl2Hm ∈ sl (Fin 2) D.L := by
  show Matrix.trace D.sl2Hm = 0
  simp [sl2Hm, Matrix.trace_fin_two]

theorem sl2Xm_mem : D.sl2Xm ∈ sl (Fin 2) D.L := by
  show Matrix.trace D.sl2Xm = 0
  simp [sl2Xm, Matrix.trace_fin_two]

theorem sl2Ym_mem : D.sl2Ym ∈ sl (Fin 2) D.L := by
  show Matrix.trace D.sl2Ym = 0
  simp [sl2Ym, Matrix.trace_fin_two]

/-- `H ∈ 𝔤_{L_E} = 𝔰𝔩_{2,L_E}`.  @census none -/
noncomputable def sl2H : sl (Fin 2) D.L := ⟨D.sl2Hm, D.sl2Hm_mem⟩

/-- `X ∈ 𝔤_{L_E}`.  @census none -/
noncomputable def sl2X : sl (Fin 2) D.L := ⟨D.sl2Xm, D.sl2Xm_mem⟩

/-- `Y ∈ 𝔤_{L_E}`.  @census none -/
noncomputable def sl2Y : sl (Fin 2) D.L := ⟨D.sl2Ym, D.sl2Ym_mem⟩

/-- `σ ∈ G_E` acting on the entries of a matrix in `𝔤_{L_E} = 𝔰𝔩_{2,L_E}` (`Matrix.map σ`; it
preserves the trace).  It is `E`-linear and `L_E`-semilinear.

@census none
-/
def galSl (σ : D.L ≃ₐ[E] D.L) (x : sl (Fin 2) D.L) : sl (Fin 2) D.L :=
  ⟨(x : Matrix (Fin 2) (Fin 2) D.L).map σ, by
    have h : Matrix.trace (x : Matrix (Fin 2) (Fin 2) D.L) = 0 := x.2
    show Matrix.trace ((x : Matrix (Fin 2) (Fin 2) D.L).map σ) = 0
    rw [Matrix.trace_fin_two] at h ⊢
    simp only [Matrix.map_apply]
    rw [← map_add, h, map_zero]⟩

@[simp] theorem galSl_coe (σ : D.L ≃ₐ[E] D.L) (x : sl (Fin 2) D.L) :
    ((D.galSl σ x : sl (Fin 2) D.L) : Matrix (Fin 2) (Fin 2) D.L) =
      (x : Matrix (Fin 2) (Fin 2) D.L).map σ := rfl

/-- `𝔰𝔩_{2,E} → 𝔰𝔩_{2,L_E}`, entrywise `algebraMap E L_E`: the inclusion of `𝔤_E` into `𝔤_{L_E}`.

@census none
-/
def sl2EIn (B : sl (Fin 2) E) : sl (Fin 2) D.L :=
  ⟨(B : Matrix (Fin 2) (Fin 2) E).map (algebraMap E D.L), by
    have h : Matrix.trace (B : Matrix (Fin 2) (Fin 2) E) = 0 := B.2
    show Matrix.trace ((B : Matrix (Fin 2) (Fin 2) E).map (algebraMap E D.L)) = 0
    rw [Matrix.trace_fin_two] at h ⊢
    simp only [Matrix.map_apply]
    rw [← map_add, h, map_zero]⟩

theorem sl2EIn_injective : Function.Injective D.sl2EIn := by
  intro A B h
  apply Subtype.ext
  ext i j
  exact (algebraMap E D.L).injective (congrFun (congrFun (congrArg Subtype.val h) i) j)

/-- `sl2EIn` respects brackets (`𝔤_E ⊆ 𝔤_{L_E}` as Lie algebras).  @census none -/
theorem sl2EIn_lie (A B : sl (Fin 2) E) : D.sl2EIn ⁅A, B⁆ = ⁅D.sl2EIn A, D.sl2EIn B⁆ := by
  apply Subtype.ext
  show ((A : Matrix (Fin 2) (Fin 2) E) * B - B * A).map (algebraMap E D.L) = _
  rw [sl_bracket]
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul]; rfl

theorem sl2EIn_add (A B : sl (Fin 2) E) : D.sl2EIn (A + B) = D.sl2EIn A + D.sl2EIn B := by
  apply Subtype.ext; exact Matrix.map_add _ (map_add _) _ _

theorem sl2EIn_smul (e : E) (A : sl (Fin 2) E) :
    D.sl2EIn (e • A) = algebraMap E D.L e • D.sl2EIn A := by
  apply Subtype.ext; ext i j; simp [sl2EIn, Algebra.smul_def]

section CharZero

variable [CharZero E]

/-- **The triple over `L_E`** (`RQ2-3.10-C5`, with `C2` over `L_E`): reading the entry `i` as
`√-1 ∈ L_E`, the matrices `H`, `X`, `Y` lie in `𝔤_{L_E} = 𝔰𝔩_{2,L_E}` (they are typed there) and
form an `sl₂` triple, `[H,X] = 2X`, `[H,Y] = -2Y`, `[X,Y] = H` (mathlib's `IsSl2Triple`, as for
`sl2Triple`).

@census    none (auxiliary; discharges clauses `RQ2-3.10-H1`, `RQ2-3.10-C5` of `RQ2-3.10`)
@source    def:sltwotriple
@clauses   RQ2-3.10-H1, RQ2-3.10-C5
@imports   none
@divergence JUSTIFIED_REFORMULATION (`L_E` as an `ImagUnit E` datum, as in `def:sqrtminusone`,
`RQ2-3.13`; disclosed there).  `𝔤_{L_E}` is mathlib's `sl (Fin 2) D.L`.
-/
theorem sl2TripleOver : IsSl2Triple D.sl2H D.sl2X D.sl2Y := by
  have hi := D.i_mul_i
  constructor
  · intro h
    have h2 : D.sl2Hm 0 1 = (0 : Matrix (Fin 2) (Fin 2) D.L) 0 1 := by
      rw [show D.sl2Hm = ((D.sl2H : sl (Fin 2) D.L) : Matrix (Fin 2) (Fin 2) D.L) from rfl, h]; rfl
    simp [sl2Hm] at h2
    exact D.i_ne_zero h2
  · apply Subtype.ext
    rw [sl_bracket]
    show D.sl2Xm * D.sl2Ym - D.sl2Ym * D.sl2Xm = D.sl2Hm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2Xm, sl2Ym, sl2Hm] <;> field_simp <;> ring1
  · rw [two_nsmul]
    apply Subtype.ext
    rw [sl_bracket]
    show D.sl2Hm * D.sl2Xm - D.sl2Xm * D.sl2Hm = D.sl2Xm + D.sl2Xm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2Xm, sl2Hm] <;> field_simp <;>
      first | ring1 | linear_combination (2 : D.L) * hi | linear_combination (-2 : D.L) * hi
  · rw [two_nsmul]
    apply Subtype.ext
    rw [sl_bracket]
    show D.sl2Hm * D.sl2Ym - D.sl2Ym * D.sl2Hm = -(D.sl2Ym + D.sl2Ym)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2Ym, sl2Hm] <;> field_simp <;>
      first | ring1 | linear_combination (2 : D.L) * hi | linear_combination (-2 : D.L) * hi

theorem sl2_linearIndependentOver : LinearIndependent D.L ![D.sl2H, D.sl2X, D.sl2Y] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 : g 0 • D.sl2Hm + g 1 • D.sl2Xm + g 2 • D.sl2Ym = 0 := by
    have h := congrArg (fun x : sl (Fin 2) D.L => (x : Matrix (Fin 2) (Fin 2) D.L)) hg
    simpa [Fin.sum_univ_three, sl2H, sl2X, sl2Y] using h
  have e00 := congrFun (congrFun h0 0) 0
  have e01 := congrFun (congrFun h0 0) 1
  have e10 := congrFun (congrFun h0 1) 0
  simp [sl2Hm, sl2Xm, sl2Ym] at e00 e01 e10
  have hd : D.i * (g 1 - g 2) = 0 := by linear_combination -(e01 + e10)
  have h12 : g 1 - g 2 = 0 := (mul_eq_zero.mp hd).resolve_left D.i_ne_zero
  have hs : g 1 + g 2 = 0 := by linear_combination 2 * e00
  have hg1 : g 1 = 0 := by linear_combination (h12 + hs) / 2
  have hg2 : g 2 = 0 := by linear_combination (hs - h12) / 2
  have hg0 : g 0 * D.i = 0 := by
    linear_combination -e10 - (2⁻¹ * D.i) * hg1 + (2⁻¹ * D.i) * hg2
  have hg0' : g 0 = 0 := (mul_eq_zero.mp hg0).resolve_right D.i_ne_zero
  intro i
  fin_cases i <;> assumption

theorem sl2_span_topOver : ⊤ ≤ Submodule.span D.L (Set.range ![D.sl2H, D.sl2X, D.sl2Y]) := by
  rintro x -
  obtain ⟨A, hA⟩ := x
  rw [Submodule.mem_span_range_iff_exists_fun]
  have htr : Matrix.trace A = 0 := hA
  rw [Matrix.trace_fin_two] at htr
  have hi := D.i_mul_i
  refine ⟨![D.i * (A 1 0 - A 0 1) / 2, A 0 0 + D.i * (A 0 1 + A 1 0) / 2,
    A 0 0 - D.i * (A 0 1 + A 1 0) / 2], ?_⟩
  apply Subtype.ext
  ext i j
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  fin_cases i <;> fin_cases j
  · simp [sl2H, sl2X, sl2Y, sl2Hm, sl2Xm, sl2Ym]; ring
  · simp [sl2H, sl2X, sl2Y, sl2Hm, sl2Xm, sl2Ym]
    linear_combination (-(A 0 1)) * hi
  · simp [sl2H, sl2X, sl2Y, sl2Hm, sl2Xm, sl2Ym]
    linear_combination (-(A 1 0)) * hi
  · simp [sl2H, sl2X, sl2Y, sl2Hm, sl2Xm, sl2Ym]
    linear_combination -htr

/-- `H`, `X`, `Y` are an `L_E`-basis of `𝔤_{L_E} = 𝔰𝔩_{2,L_E}` (the `L_E`-analogue of
`sl2_isBasis`, which carries `RQ2-3.10-C1` over `ℂ`); in particular `𝔤_{L_E}` is their `L_E`-span.

@census none (helper)
-/
theorem sl2_isBasisOver :
    ∃ b : Module.Basis (Fin 3) D.L (sl (Fin 2) D.L), ⇑b = ![D.sl2H, D.sl2X, D.sl2Y] :=
  ⟨Module.Basis.mk D.sl2_linearIndependentOver D.sl2_span_topOver, Module.Basis.coe_mk _ _⟩

/-- `σH = χ_E(σ)·H` for every `σ ∈ G_E`.  @census none (helper) -/
theorem galSl_sl2H (σ : D.L ≃ₐ[E] D.L) :
    D.galSl σ D.sl2H = ((D.chi σ : ℤ) : D.L) • D.sl2H := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2H, sl2Hm, D.chi_spec σ]

/-- For `σ ∈ G_E` with `χ_E(σ) = -1`: `σH = -H`, `σX = Y`, `σY = X`.  @census none (helper) -/
theorem galSl_triple_of_chi_neg_one {σ : D.L ≃ₐ[E] D.L} (hσ : D.chi σ = -1) :
    D.galSl σ D.sl2H = -D.sl2H ∧ D.galSl σ D.sl2X = D.sl2Y ∧ D.galSl σ D.sl2Y = D.sl2X := by
  have h := D.chi_eq_neg_one_iff.mp hσ
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [sl2H, sl2X, sl2Y, sl2Hm, sl2Xm, sl2Ym, h, map_inv₀, map_ofNat])

/-- For `σ ∈ G_E` with `χ_E(σ) = 1`: `σ` fixes `H`, `X`, `Y`.  @census none (helper) -/
theorem galSl_triple_of_chi_one {σ : D.L ≃ₐ[E] D.L} (hσ : D.chi σ = 1) :
    D.galSl σ D.sl2H = D.sl2H ∧ D.galSl σ D.sl2X = D.sl2X ∧ D.galSl σ D.sl2Y = D.sl2Y := by
  have h := D.chi_eq_one_iff.mp hσ
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [sl2H, sl2X, sl2Y, sl2Hm, sl2Xm, sl2Ym, h, map_inv₀, map_ofNat])

/-- `√-1 ∈ E` ⇒ every `σ ∈ G_E` fixes `H`, `X`, `Y`.  @census none (helper) -/
theorem galSl_triple_of_sqrt (hE : ∃ a : E, a * a = -1) (σ : D.L ≃ₐ[E] D.L) :
    D.galSl σ D.sl2H = D.sl2H ∧ D.galSl σ D.sl2X = D.sl2X ∧ D.galSl σ D.sl2Y = D.sl2Y :=
  D.galSl_triple_of_chi_one (D.chi_eq_one_of_sqrt hE σ)

/-- `RQ2-3.10-C3`: if `√-1 ∉ E`, complex conjugation `c ∈ G_E` (`ImagUnit.conj`) acts on matrix
entries by `cH = -H`, `cX = Y`, `cY = X`.

@census    none (auxiliary; discharges clause `RQ2-3.10-C3` of `RQ2-3.10`)
@source    def:sltwotriple
@clauses   RQ2-3.10-C3
@imports   none
@divergence none
-/
theorem galSl_conj_triple (hE : ¬ ∃ a : E, a * a = -1) :
    D.galSl (D.conj hE) D.sl2H = -D.sl2H ∧ D.galSl (D.conj hE) D.sl2X = D.sl2Y ∧
      D.galSl (D.conj hE) D.sl2Y = D.sl2X :=
  D.galSl_triple_of_chi_neg_one (D.chi_conj hE)

/-- `RQ2-3.10-C4`: the `E`-rational form of `𝔤_{L_E}` cut out by the entrywise action of `G_E` —
the trace-zero matrices over `L_E` fixed by every `σ ∈ G_E` — **is** `𝔤_E = 𝔰𝔩_{2,E}`, embedded by
`sl2EIn` (an injective, bracket-preserving `E`-linear map: `sl2EIn_injective`, `sl2EIn_lie`,
`sl2EIn_add`, `sl2EIn_smul`).  For `E = ℚ` this is `𝔰𝔩_{2,ℚ}` (cf. `rationalForm_eq_sl2Q`).

@census    none (auxiliary; discharges clause `RQ2-3.10-C4` of `RQ2-3.10`)
@source    def:sltwotriple
@clauses   RQ2-3.10-C4
@imports   none
@divergence none (stated without the hypothesis `√-1 ∉ E`, under which the tex states it; for
`√-1 ∈ E` it holds trivially, `G_E` being trivial).  `𝔤_{L_E}` is `sl (Fin 2) D.L`, which is the
`L_E`-span of `H`, `X`, `Y` (`sl2_isBasisOver`).
-/
theorem rationalForm_eq_range :
    {x : sl (Fin 2) D.L | ∀ σ : D.L ≃ₐ[E] D.L, D.galSl σ x = x} = Set.range D.sl2EIn := by
  ext x
  constructor
  · intro hx
    have hent : ∀ i j, (x : Matrix (Fin 2) (Fin 2) D.L) i j ∈ Set.range (algebraMap E D.L) := by
      intro i j
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro σ
      exact congrFun (congrFun (congrArg Subtype.val (hx σ)) i) j
    choose R hR using hent
    have htr : Matrix.trace (Matrix.of R) = 0 := by
      have h : Matrix.trace (x : Matrix (Fin 2) (Fin 2) D.L) = 0 := x.2
      rw [Matrix.trace_fin_two] at h ⊢
      apply (algebraMap E D.L).injective
      simp only [Matrix.of_apply, map_add, hR, map_zero, h]
    refine ⟨⟨Matrix.of R, htr⟩, Subtype.ext ?_⟩
    ext i j
    exact hR i j
  · rintro ⟨B, rfl⟩ σ
    apply Subtype.ext
    ext i j
    simp [sl2EIn]

/-- `RQ2-3.10-C6`: if `√-1 ∈ E`, then `H`, `X`, `Y` lie in `𝔤_E = 𝔰𝔩_{2,E}` (in the image of
`sl2EIn`).

@census    none (auxiliary; discharges clause `RQ2-3.10-C6` of `RQ2-3.10`)
@source    def:sltwotriple
@clauses   RQ2-3.10-C6
@imports   none
@divergence none
-/
theorem triple_mem_range_of_sqrt (hE : ∃ a : E, a * a = -1) :
    D.sl2H ∈ Set.range D.sl2EIn ∧ D.sl2X ∈ Set.range D.sl2EIn ∧ D.sl2Y ∈ Set.range D.sl2EIn := by
  rw [← D.rationalForm_eq_range]
  exact ⟨fun σ => (D.galSl_triple_of_sqrt hE σ).1, fun σ => (D.galSl_triple_of_sqrt hE σ).2.1,
    fun σ => (D.galSl_triple_of_sqrt hE σ).2.2⟩

/-- `RQ2-3.09-C4` (the `𝔤_E` half): the three elements `iH`, `X + Y`, `i(X - Y)` of `𝔤_{L_E}` lie in
the `E`-form `𝔤_E = 𝔰𝔩_{2,E}` (the image of `sl2EIn`) — for every `E`, whether or not `√-1 ∈ E`: each
is fixed by every `σ ∈ G_E` (`σ(i) = ±i`, and for `σ(i) = -i` both factors change sign or `X`, `Y`
are swapped), so `rationalForm_eq_range` applies.  Together with `casimirOf_mem_adjoin`
(`HC/Casimir.lean`) at `K := E`, `i := D.i`, whose generators are exactly these three elements, this
gives `C = H² - 2H + 4XY + 1 ∈ U(𝔤_E)`: `C` lies in the `E`-subalgebra generated by the image of
`𝔤_E`.

@census    none (auxiliary; discharges clause `RQ2-3.09-C4` of `RQ2-3.09`)
@source    prop:casimirdescends
@clauses   RQ2-3.09-C4
@imports   none
@divergence none
-/
theorem rationalTriple_mem_range :
    D.i • D.sl2H ∈ Set.range D.sl2EIn ∧ D.sl2X + D.sl2Y ∈ Set.range D.sl2EIn ∧
      D.i • (D.sl2X - D.sl2Y) ∈ Set.range D.sl2EIn := by
  have hi := D.i_mul_i
  simp only [← D.rationalForm_eq_range, Set.mem_setOf_eq]
  refine ⟨fun σ => ?_, fun σ => ?_, fun σ => ?_⟩ <;>
  rcases D.apply_i σ with h | h <;>
    (apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;>
      simp [sl2H, sl2X, sl2Y, sl2Hm, sl2Xm, sl2Ym, h, map_inv₀, map_ofNat, hi] <;> ring)

end CharZero

end ImagUnit

/-! ## §3.3 — the isotypic bookkeeping `M_n = M[χ_n]` -/

variable (E : Type u) [Field E] (M : Type v) [AddCommGroup M] [Module E M]

/-- The `§3.3` bookkeeping the whole of `§3.4` runs on: an `E`-vector space `M` decomposed into the
`SO(2)`-isotypic components `M_n = M[χ_n]` (`comp`), together with the action of the classical
triple, `H` acting on `M_n` by the scalar `n`, `X` raising the index by `2` and `Y` lowering it by
`2`.

This is **not** mathlib's `LieModule.weightSpace` (ledger `MD-S7-01`) and it is not a Harish-Chandra
module either: finite generation and admissibility are `RQ2-3.11`'s
(`RationalQuivers/HC/Classical.lean`), which is stated on top of this.

@census none
-/
structure WeightData where
  /-- `M_n := M[χ_n]`, the `χ_n`-isotypic component (`RQ2-3.11-C2`'s `M_n`). -/
  comp : ℤ → Submodule E M
  /-- `M = ⨁_{n ∈ ℤ} M_n` (`RQ2-3.11-C3`). -/
  isInternal : DirectSum.IsInternal comp
  /-- `H`, acting on `M`. -/
  H : Module.End E M
  /-- `X`, acting on `M`. -/
  X : Module.End E M
  /-- `Y`, acting on `M`. -/
  Y : Module.End E M
  /-- `H` acts on `M_n` by the scalar `n`; see the module docstring for why this is forced. -/
  H_apply : ∀ (n : ℤ) (v : M), v ∈ comp n → H v = (n : E) • v
  /-- `X : M_n → M_{n+2}`. -/
  X_mem : ∀ (n : ℤ) (v : M), v ∈ comp n → X v ∈ comp (n + 2)
  /-- `Y : M_n → M_{n-2}`. -/
  Y_mem : ∀ (n : ℤ) (v : M), v ∈ comp n → Y v ∈ comp (n - 2)
  /-- `[H,X] = 2X`. -/
  lie_H_X : H * X - X * H = (2 : E) • X
  /-- `[H,Y] = -2Y`. -/
  lie_H_Y : H * Y - Y * H = -((2 : E) • Y)
  /-- `[X,Y] = H`. -/
  lie_X_Y : X * Y - Y * X = H

variable {E M}

namespace WeightData

variable (W : WeightData E M)

theorem isInternal' : DirectSum.IsInternal W.comp := W.isInternal

theorem H_apply' (n : ℤ) (v : M) (hv : v ∈ W.comp n) : W.H v = (n : E) • v := W.H_apply n v hv

theorem X_mem' (n : ℤ) (v : M) (hv : v ∈ W.comp n) : W.X v ∈ W.comp (n + 2) := W.X_mem n v hv

theorem Y_mem' (n : ℤ) (v : M) (hv : v ∈ W.comp n) : W.Y v ∈ W.comp (n - 2) := W.Y_mem n v hv

theorem lie_H_X' : W.H * W.X - W.X * W.H = (2 : E) • W.X := W.lie_H_X

theorem lie_H_Y' : W.H * W.Y - W.Y * W.H = -((2 : E) • W.Y) := W.lie_H_Y

theorem lie_X_Y' : W.X * W.Y - W.Y * W.X = W.H := W.lie_X_Y

/-- The **Casimir** `C = H² - 2H + 4XY + 1 ∈ U(𝔤)`, as it acts on `M` (`§3.3`).

@census none
-/
def casimir : Module.End E M := W.H ^ 2 - 2 * W.H + 4 * (W.X * W.Y) + 1

/-- `C` applied to a vector, in terms of the three operators — the form every `§3.4` computation
uses.

@census none
-/
theorem casimir_apply (v : M) :
    W.casimir v = W.H (W.H v) - (2 : E) • W.H v + (4 : E) • W.X (W.Y v) + v := by
  show ((W.H ^ 2 - 2 * W.H + 4 * (W.X * W.Y) + 1 : Module.End E M)) v = _
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, pow_two,
    Module.End.one_apply, Module.End.ofNat_apply, ← Nat.cast_smul_eq_nsmul E]
  norm_num

/-- `[H,X] = 2X` with the ring numeral `2` rather than the scalar `(2 : E)`, so that the
`Module.End`-ring tactics can use it.

@census none
-/
theorem H_mul_X_numeral : W.H * W.X - W.X * W.H = 2 * W.X := by
  rw [W.lie_H_X, two_smul, two_mul]

/-- `[H,Y] = -2Y`, as a ring identity; see `H_mul_X_numeral`.

@census none
-/
theorem H_mul_Y_numeral : W.H * W.Y - W.Y * W.H = -(2 * W.Y) := by
  rw [W.lie_H_Y, two_smul, two_mul]

/-- **`C` is central**: `[C,X] = 0`.  This is the only property of the Casimir the whole of `§3.4`
uses, and it follows from `[H,X] = 2X` and `[X,Y] = H` alone.

@census none
-/
theorem casimir_commute_X : Commute W.casimir W.X := by
  show (W.H ^ 2 - 2 * W.H + 4 * (W.X * W.Y) + 1) * W.X
      = W.X * (W.H ^ 2 - 2 * W.H + 4 * (W.X * W.Y) + 1)
  linear_combination (norm := noncomm_ring) W.H * W.H_mul_X_numeral + W.H_mul_X_numeral * W.H
    - 4 * W.X * W.lie_X_Y

/-- `[C,Y] = 0`; see `casimir_commute_X`.

@census none
-/
theorem casimir_commute_Y : Commute W.casimir W.Y := by
  show (W.H ^ 2 - 2 * W.H + 4 * (W.X * W.Y) + 1) * W.Y
      = W.Y * (W.H ^ 2 - 2 * W.H + 4 * (W.X * W.Y) + 1)
  linear_combination (norm := noncomm_ring) W.H * W.H_mul_Y_numeral + W.H_mul_Y_numeral * W.H
    + 4 * W.lie_X_Y * W.Y

/-- `YX = XY - H`, the pointwise form of `[X,Y] = H`.

@census none
-/
theorem Y_X_apply (v : M) : W.Y (W.X v) = W.X (W.Y v) - W.H v := by
  have h := congrArg (fun f : Module.End E M => f v) W.lie_X_Y
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [← h]; abel

/-- **`4XY = C - k²` on `M_{k+1}`** — the `m = 1` case of `prop:XY_C_relation`, and the source's
own step: on `M_{k+1}` one has `H = k+1`, so `H² - 2H + 1 = k²`.

@census none
-/
theorem four_X_Y_apply (k : ℤ) (v : M) (hv : v ∈ W.comp (k + 1)) :
    (4 : E) • W.X (W.Y v) = W.casimir v - (((k : ℤ) : E) ^ 2) • v := by
  have hHv : W.H v = (((k + 1 : ℤ) : E)) • v := W.H_apply _ _ hv
  have hHHv : W.H (W.H v) = (((k + 1 : ℤ) : E)) ^ 2 • v := by
    rw [hHv, map_smul, hHv, smul_smul, sq]
  rw [W.casimir_apply v, hHHv, hHv]
  push_cast
  module

/-- **`4YX = C - k²` on `M_{-(k+1)}`** — the companion of `four_X_Y_apply`, from `YX = XY - H`
and `H = -(k+1)` there: `-(k+2)² + 4(k+1) = -k²`.

@census none
-/
theorem four_Y_X_apply (k : ℤ) (v : M) (hv : v ∈ W.comp (-(k + 1))) :
    (4 : E) • W.Y (W.X v) = W.casimir v - (((k : ℤ) : E) ^ 2) • v := by
  have hv' : v ∈ W.comp ((-k - 2) + 1) := by
    have he : (-k - 2) + 1 = -(k + 1) := by ring
    rwa [he]
  have h1 := W.four_X_Y_apply (-k - 2) v hv'
  have h2 : W.H v = (((-(k + 1) : ℤ)) : E) • v := W.H_apply _ _ hv
  rw [W.Y_X_apply, smul_sub, h1, h2]
  push_cast
  module

end WeightData

/-! ## G5 — a non-degenerate inhabitant of `WeightData`

`WORKFLOW.md` §4/G5 asks, in the same commit as every new `structure`, for a concrete inhabitant
and — where degeneracy is a live risk — a **non-degenerate** one.  For `WeightData` the live risk is
the all-trivial reading in which `M = 0`, or in which `X = Y = 0` so that every operator identity of
`§3.4` holds for want of anything to say.  The witness below excludes both: every component `M_n` is
one-dimensional and non-zero, `X` is injective and `Y` is injective on every `M_n` with `n ∉ {0,2}`.

It is the "free" `ℤ`-graded `𝔰𝔩₂`-module `ℚ⟨…, δ_{-1}, δ_0, δ_1, …⟩` with
`X δ_n = δ_{n+2}` and `Y δ_n = -n(n-2)/4 · δ_{n-2}`; the coefficient is forced by `[X,Y] = H`,
which asks exactly for `c_n - c_{n+2} = n`.  It is deliberately **not** a Harish-Chandra module —
it is not finitely generated — and `RationalQuivers/HC/Classical.lean` carries `RQ2-3.11`'s own
witness.
-/

section Model

open Finsupp

/-- The coefficient of `Y` on `δ_n` in `weightModelFree`, forced by `[X,Y] = H`.

@census none
-/
def freeYCoef (n : ℤ) : ℚ := -((n : ℚ) * ((n : ℚ) - 2)) / 4

theorem freeYCoef_sub (n : ℤ) : freeYCoef n - freeYCoef (n + 2) = (n : ℚ) := by
  simp only [freeYCoef, Int.cast_add, Int.cast_ofNat]
  ring

/-- `H` on the free model: `δ_n ↦ n · δ_n`.

@census none
-/
noncomputable def freeH : Module.End ℚ (ℤ →₀ ℚ) :=
  Finsupp.lsum ℕ fun n : ℤ => (n : ℚ) • Finsupp.lsingle n

/-- `X` on the free model: `δ_n ↦ δ_{n+2}`.

@census none
-/
noncomputable def freeX : Module.End ℚ (ℤ →₀ ℚ) :=
  Finsupp.lsum ℕ fun n : ℤ => Finsupp.lsingle (n + 2)

/-- `Y` on the free model: `δ_n ↦ c_n · δ_{n-2}`.

@census none
-/
noncomputable def freeY : Module.End ℚ (ℤ →₀ ℚ) :=
  Finsupp.lsum ℕ fun n : ℤ => freeYCoef n • Finsupp.lsingle (n - 2)

theorem freeH_single (n : ℤ) (a : ℚ) :
    freeH (Finsupp.single n a) = Finsupp.single n ((n : ℚ) * a) := by
  rw [freeH, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.smul_single, smul_eq_mul]

theorem freeX_single (n : ℤ) (a : ℚ) :
    freeX (Finsupp.single n a) = Finsupp.single (n + 2) a := by
  rw [freeX, Finsupp.lsum_single, Finsupp.lsingle_apply]

theorem freeY_single (n : ℤ) (a : ℚ) :
    freeY (Finsupp.single n a) = Finsupp.single (n - 2) (freeYCoef n * a) := by
  rw [freeY, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.smul_single, smul_eq_mul]

/-- **G5 witness for `WeightData`** (`WORKFLOW.md` §4/G5.1–G5.2): the free `ℤ`-graded `𝔰𝔩₂`-module
over `ℚ`.  Non-degenerate: `comp n ≠ ⊥` for every `n`, and `X ≠ 0 ≠ Y`.

@census none
-/
noncomputable def weightModelFree : WeightData ℚ (ℤ →₀ ℚ) where
  comp n := LinearMap.range (Finsupp.lsingle (M := ℚ) n)
  isInternal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    exact ⟨iSupIndep_range_lsingle ℤ ℚ ℚ, Finsupp.iSup_lsingle_range⟩
  H := freeH
  X := freeX
  Y := freeY
  H_apply := by
    rintro n v ⟨a, rfl⟩
    show freeH (Finsupp.single n a) = _
    rw [freeH_single]
    show _ = (n : ℚ) • Finsupp.single n a
    rw [Finsupp.smul_single, smul_eq_mul]
  X_mem := by
    rintro n v ⟨a, rfl⟩
    show freeX (Finsupp.single n a) ∈ _
    rw [freeX_single]
    exact ⟨a, rfl⟩
  Y_mem := by
    rintro n v ⟨a, rfl⟩
    show freeY (Finsupp.single n a) ∈ _
    rw [freeY_single]
    exact ⟨freeYCoef n * a, rfl⟩
  lie_H_X := by
    apply Finsupp.lhom_ext
    intro n a
    show freeH (freeX (Finsupp.single n a)) - freeX (freeH (Finsupp.single n a))
      = ((2 : ℚ) • freeX) (Finsupp.single n a)
    simp only [freeX_single, freeH_single, LinearMap.smul_apply, Finsupp.smul_single]
    rw [← Finsupp.single_sub]
    congr 1
    push_cast
    ring
  lie_H_Y := by
    apply Finsupp.lhom_ext
    intro n a
    show freeH (freeY (Finsupp.single n a)) - freeY (freeH (Finsupp.single n a))
      = (-((2 : ℚ) • freeY)) (Finsupp.single n a)
    simp only [freeY_single, freeH_single, LinearMap.neg_apply, LinearMap.smul_apply,
      Finsupp.smul_single]
    rw [← Finsupp.single_sub, ← Finsupp.single_neg]
    congr 1
    push_cast
    ring
  lie_X_Y := by
    apply Finsupp.lhom_ext
    intro n a
    show freeX (freeY (Finsupp.single n a)) - freeY (freeX (Finsupp.single n a))
      = freeH (Finsupp.single n a)
    rw [freeY_single, freeX_single, freeX_single, freeY_single, freeH_single,
      show n - 2 + 2 = n by ring, show n + 2 - 2 = n by ring, ← Finsupp.single_sub,
      ← sub_mul, freeYCoef_sub]

/-- Non-degeneracy, half one: every isotypic component of the witness is non-zero, so the
`∀ v ∈ M_n` statements of `§3.4` are not vacuously true.

@census none
-/
theorem weightModelFree_comp_ne_bot (n : ℤ) : weightModelFree.comp n ≠ ⊥ := by
  intro h
  have h1 : (Finsupp.single n (1 : ℚ)) ∈ weightModelFree.comp n := ⟨1, rfl⟩
  rw [h, Submodule.mem_bot] at h1
  have := DFunLike.congr_fun h1 n
  rw [Finsupp.single_eq_same] at this
  exact one_ne_zero this

/-- Non-degeneracy, half two: the raising and lowering operators of the witness are non-zero, so the
witness does not satisfy `§3.4` by having nothing to say.

@census none
-/
theorem weightModelFree_X_ne_zero : weightModelFree.X ≠ 0 := by
  intro h
  have : freeX (Finsupp.single (0 : ℤ) (1 : ℚ)) = 0 := by
    show weightModelFree.X _ = 0
    rw [h]; rfl
  rw [freeX_single] at this
  have h2 := DFunLike.congr_fun this ((0 : ℤ) + 2)
  rw [Finsupp.single_eq_same] at h2
  exact one_ne_zero h2

/-! ### The one-component `WeightData`

A second, deliberately small inhabitant, used by `HC/Classical.lean` (`RQ2-3.11`'s witness) and
`HC/Normalization.lean` (`§3.4`'s standing setup): everything sits in `M_0`, all three operators are
zero.  It is *not* non-degenerate in the operator sense — that is what `weightModelFree` is for —
but it is the shape a **finitely generated, admissible** module has to have if it is to be small,
and finite generation is what `weightModelFree` cannot offer.
-/

/-- The one-component family: `⊤` at `0`, `⊥` elsewhere.

@census none
-/
def topAtZero (E : Type u) [Field E] (M : Type v) [AddCommGroup M] [Module E M] (n : ℤ) :
    Submodule E M := if n = 0 then ⊤ else ⊥

variable {E : Type u} [Field E] {M : Type v} [AddCommGroup M] [Module E M]

theorem topAtZero_zero : topAtZero E M 0 = ⊤ := by simp [topAtZero]

theorem topAtZero_ne_zero {n : ℤ} (hn : n ≠ 0) : topAtZero E M n = ⊥ := by simp [topAtZero, hn]

theorem mem_topAtZero_zero (v : M) : v ∈ topAtZero E M 0 := by rw [topAtZero_zero]; trivial

theorem topAtZero_isInternal : DirectSum.IsInternal (topAtZero E M) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨fun i => ?_, le_antisymm le_top (le_iSup_of_le 0 (by rw [topAtZero_zero]))⟩
  by_cases h : i = 0
  · subst h
    have hb : (⨆ j, ⨆ _ : j ≠ (0 : ℤ), topAtZero E M j) = ⊥ :=
      le_antisymm (iSup_le fun j => iSup_le fun hj => (topAtZero_ne_zero hj).le) bot_le
    rw [hb]
    exact disjoint_bot_right
  · rw [topAtZero_ne_zero h]
    exact disjoint_bot_left

/-- The `WeightData` concentrated in degree `0`, with all three operators zero.

@census none
-/
def trivialWeightData (E : Type u) [Field E] (M : Type v) [AddCommGroup M] [Module E M] :
    WeightData E M where
  comp := topAtZero E M
  isInternal := topAtZero_isInternal
  H := 0
  X := 0
  Y := 0
  H_apply n v hv := by
    by_cases h : n = 0
    · subst h; simp
    · have hv' : v ∈ topAtZero E M n := hv
      rw [topAtZero_ne_zero h, Submodule.mem_bot] at hv'
      subst hv'; simp
  X_mem n v _ := by simp
  Y_mem n v _ := by simp
  lie_H_X := by simp
  lie_H_Y := by simp
  lie_X_Y := by simp

/-- On the one-component `WeightData` the Casimir is the identity, so it has generalized
infinitesimal character `λ = 1 = 1²` — i.e. `ℓ = 1`.

@census none
-/
theorem trivialWeightData_casimir : (trivialWeightData E M).casimir = 1 := by
  show (0 : Module.End E M) ^ 2 - 2 * 0 + 4 * (0 * 0) + 1 = 1
  simp

end Model

end RationalQuivers.HC
