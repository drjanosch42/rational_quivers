import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import RationalQuivers.HC.Pair
import RationalQuivers.HC.Casimir
import RationalQuivers.HC.Graded
import RationalQuivers.HC.Noetherian
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Harish-Chandra modules for `SL₂(ℝ)`, and the category `HC_λ(𝔤,K)_E`

Formalizes the two `§3.3` definitions of `latex/rational_quivers.tex` that describe the *categories*
(census `RQ2-3.11`, `RQ2-3.03`; stage **S7**).

## Main definitions / results

* `RationalQuivers.HC.chiChar` — the character `χ_n` of `SO(2,ℝ)` of `§3.3`, **as displayed**,
  `χ_n(ξ,η) = (ξ + iη)^n`, under the author's ruling of 2026-09-10 (see below; it supersedes
  coordinator ruling `R-S7-6`, which had moved a sign into this character instead);
  `RationalQuivers.HC.rot` — the one-parameter subgroup `t ↦ exp(tW)` of `SO(2,ℝ)`.
* `RationalQuivers.HC.HarishChandraModule` — census `RQ2-3.11`: a complex `(𝔤,K)`-module that is
  finitely generated and admissible, with `M = ⨁_{n ∈ ℤ} M_n`; the `(𝔤,K)`-compatibility
  conditions are the field `differential` (condition (i)) and the entailed
  `HarishChandraModule.compat_generators` (condition (ii)).
* `RationalQuivers.HC.HCObj`, `HCHom`, `harishChandraCat_abelian` — the category `HC(𝔤,K)` and the
  claim that it is abelian (clause `RQ2-3.11-C4`).
* `RationalQuivers.HC.Category` — census `RQ2-3.03`: `HC_λ(𝔤,K)_E`, the full subcategory of those
  objects with generalized infinitesimal character `λ = ℓ²` on which `-1₂` acts by `(-1)^{ℓ-1}`.
* `RationalQuivers.HC.categoryOver` — a generic full-subcategory construction on the **imported**
  category `HCInterface.cat E`, for a general base field `E/ℚ`; it renders no census clause (see
  its docstring and the `@divergence` on `Category`).
* `RationalQuivers.HC.stdHC` — the G5 witness that exercises the sign convention: the standard
  representation `F_2 = ℂ²` (weights `±1`), an object of `HC_λ` at `ℓ = 2`.

## Implementation notes

**The sign convention — the AUTHOR'S RULING of 2026-09-10, which SUPERSEDES coordinator ruling
`R-S7-6` (2026-09-02; verifier finding V-S7-5).**

*The problem, as the source posed it until 2026-09-11.*  Until the author's own `latex/` edit
landed at **`17fae88`, 2026-09-11**, the source displayed `H = !![0, -i; i, 0]` together with the
parametrisation `(ξ,η) ↦ !![ξ, -η; η, ξ]` of `SO(2)` and `χ_n(!![ξ, -η; η, ξ]) = (ξ + iη)^n`.  Those
three were inconsistent by a sign with `§3.4`: with `W = !![0, -1; 1, 0]` the generator of the
displayed parametrisation (`rot t = exp(tW)`), **that** `H` was `i·W`, `dχ_n(W) = i·n`, hence in any
`(𝔤,K)`-module whose `𝔨`-action is the differential of the `K`-action, `H` would have acted on
`M[χ_n]` by `−n` — while the proof of `prop:XY_C_relation` and `AN-22` require `H|_{M_n} = +n`
(`WeightData.H_apply`, `HC/Sl2.lean`).  Of those three displays only `H` moved: the parametrisation
and `χ_n` are displayed today exactly as they were.  Until 2026-09-11 this paragraph opened *"The
problem, unchanged.  The source displays `H = !![0, -i; i, 0]` …"* — true when written, falsified by
`17fae88`, superseded and not deleted (`R-PROC-2` item 7).

*The RETIRED repair (`R-S7-6`), recorded because it is not deleted.*  `R-S7-6` kept the source's
matrices verbatim and moved the sign into the character, rendering `chiChar n (ξ,η) := (ξ − iη)^n`
— one sign against clause `RQ2-3.11-H2`'s "`χ_n` as displayed", disclosed as a
`JUSTIFIED_REFORMULATION` on `HarishChandraModule`.

*The ruling in force.*  The paper's author ruled on 2026-09-10 the other way, and the ruling is
what this file now renders:

* `H ↦ −H` — the explicit matrix is negated, so `sl2Hm = !![0, i; -i, 0]`;
* the explicit `X` and `Y` **matrices are swapped**;
* `χ_n = (ξ + iη)^n` is **unchanged** — which is the point of the ruling: it keeps `M_+` the
  holomorphic discrete series and `M_−` its anti-holomorphic twin, and it makes clause
  `RQ2-3.11-H2`'s "`χ_n` as displayed" literally true, so the `JUSTIFIED_REFORMULATION` is
  **retired** rather than reworded.

Consequently `H = −i·W`, `dχ_n(W) = i·n` and `H|_{M_n} = +n`, and `X` raises `n` by `2` — which is
what `§3.4` needs.  The renormalization is an **automorphism of `𝔰𝔩₂`**, inner over `ℂ`, so every
relation the source displays holds of the new triple verbatim: `[H,X] = 2X`, `[H,Y] = −2Y`,
`[X,Y] = H` (`:1565`), `cH = −H`, `cX = Y`, `cY = X` (`:1569`) and the Casimir display (`:1573`)
are all unchanged, and `C = H² − 2H + 4XY + 1` is the same element of `U(𝔤)`.

*What the paper says — the divergence is OVER.*  `latex/` is **not** edited by this stage — it is
the author's alone (`WORKFLOW.md` §2) — so this amendment could only wait for the author's own
commit.  It landed at **`17fae88`, 2026-09-11**: `:1559-1561` now displays the ruled triple, and the
paper and this tree agree entry for entry — checked **symbolically**, parsing both sides rather than
retyping either, and **negative-controlled** against the pre-edit `.tex` at `ae2e6e2`, where all
three matrices come out DIFFERENT.  Until 2026-09-11 this passage read: *"**What the paper still
says.**  `latex/` is **not** edited by this stage — it is the author's alone (`WORKFLOW.md` §2) — so
between this amendment and the author's own commit the paper displays the pre-ruling triple at
`:1559-1561` and the Lean displays the ruled one.  That divergence is deliberate, is disclosed in
`workflow/stages/S7/FREEZE.md`'s post-freeze amendment entry, and ends when the author's edit
lands."* — superseded, kept because a superseded reason is recorded and never deleted (`R-PROC-2`
item 7).  The window in which they did disagree is disclosed in
`workflow/stages/S7/FREEZE.md`'s post-freeze amendment entries, not here.

The G5 witness `stdHC` below has `M_{±1} ≠ 0` **and** a `K`-action whose derivative matches `H`,
so the convention is exercised, not merely consistent in degree `0`.

**The `(𝔤,K)`-compatibility: one field, one entailed statement.**  A `(𝔤,K)`-module satisfies
(i) the `𝔨`-action is the differential of the `K`-action, and (ii) `k·(x·v) = (Ad(k)x)·(k·v)`.
Condition (i) is the field `HarishChandraModule.differential`: `𝔨_ℂ = ℂ·W` with `W = iH` (the
ruling's `H = −i·W`), and on `M_n` (finite-dimensional, `rep (rot t) v = χ_n(rot t)·v` by
`isotypic`) the derivative at `t = 0` of `t ↦ rep (rot t) v` is `χ_n'(0)·v`, so (i) reads
`i·H v = χ_n'(0)·v`, i.e. `H v = (−i·χ_n'(0))·v`, which is what the field says (`M` carries no
topology, so the derivative is taken of the scalar function, which is what it is on a
finite-dimensional isotypic component).  Under the displayed `χ_n` the ruling restores,
`χ_n'(0) = +i·n` and the field agrees with `H_apply` (`WeightData.differential_of_chiChar`); with
the source's ORIGINAL `H` and the displayed `χ_n` together it would force `H v = −n·v`, and every
inhabitant would be concentrated in degree `0` — that inconsistency is what the ruling removes,
and it removes it by moving `H`, not `χ_n`.  Condition (ii) on the generators is
`HarishChandraModule.compat_generators`, a G2 statement **proved at G4** (`5094d2a`; dated
correction 2026-09-02, G4 verification finding `V-S7G4-1` — it read "(sorry-bodied)" here) — it
**is** entailed by
`isotypic` + `X_mem`/`Y_mem` + `isInternal` and `χ_a χ_b = χ_{a+b}`, given the matrix fact
`ad_so2Matrix_triple` (`Ad(k)H = H`, `Ad(k)X = χ_2(k)X`, `Ad(k)Y = χ_{−2}(k)Y`, also a G2
statement) — and it is stated rather than argued in prose because the earlier prose argument
used `Ad(k)X = χ_2(k)X`, which was **false** under the `H` the source displayed until `17fae88`
(2026-09-11) taken with the displayed `χ_n`, and is true under the `H` it displays now (verifier
probes).

**`M_n` is pinned by the `K`-action, not chosen.**  `HarishChandraModule.isotypic` is an `iff`:
`v ∈ M_n` **exactly when** `k · v = χ_n(k) · v` for every `k ∈ SO(2,ℝ)`.  So the `comp` family of
the underlying `WeightData` is determined by the representation, which is what `M_n := M[χ_n]`
means; nothing here is free to choose a convenient decomposition.

**Base field of `RQ2-3.03`** — see the `@divergence` on `Category`.  The source's `E` ranges over
field extensions of `ℚ`; the concrete rendering is at `E = ℂ`, which is the base field at which the
source itself *defines* a Harish-Chandra module (`RQ2-3.11`: "a **complex** `(𝔤,K)`-module").  For a
general `E` the source's `HC_λ(𝔤,K)_E` is the **imported** category of clause `RQ-3.01-C7`, and the
full-subcategory construction on it is `categoryOver`.
-/

universe u

namespace RationalQuivers.HC

open CategoryTheory Complex

/-! ## The character `χ_n`, the one-parameter subgroup `rot`, and the central element `-1₂` -/

/-- The character `χ_n : SO(2,ℝ) → ℂ^×`, `!![ξ, -η; η, ξ] ↦ (ξ + iη)^n` (clause `RQ2-3.11-H2`), written
on the `ℝ`-points of `SO(2)_ℚ` (`HC/Pair.lean`), which `so2Matrix` identifies with the matrices
displayed in the source.

**Sign.** This definition is the character the source displays, `(ξ + iη)^n`, verbatim.  Between
2026-09-02 and 2026-09-10 it read `(ξ − iη)^n` instead, under coordinator ruling `R-S7-6`, which
moved the source's one-sign inconsistency into this character; the paper author's ruling of
2026-09-10 **supersedes** `R-S7-6` and moves it into `H` instead (`H ↦ −H`, with the explicit `X`
and `Y` matrices swapped — see the module docstring and `HC/Sl2.lean`).  So clause `RQ2-3.11-H2`'s
"`χ_n` as displayed" is now literally rendered, and `HarishChandraModule`'s
`JUSTIFIED_REFORMULATION` divergence is retired.

**Correction, 2026-09-11.**  The summary line above read `↦ (ξ - iη)^n` from 2026-09-02 until
2026-09-11.  That was a **stale leftover**, not a superseded ruling: the 2026-09-10 amendment
restored the definition below to `(ξ + iη)^n` and rewrote this *Sign* paragraph but did not follow
through to the one-line summary, so the docstring contradicted both its own body and the `def` it
documents.  Corrected in round 5 of the `R-PROC-4` prose sequence; recorded rather than silently
fixed.

@census none
-/
noncomputable def chiChar (n : ℤ) (p : SO2_QStructure ℝ) : ℂ :=
  ((p.1.1 : ℂ) + (p.1.2 : ℂ) * I) ^ n

theorem chiChar_base_ne_zero (p : SO2_QStructure ℝ) : ((p.1.1 : ℂ) + (p.1.2 : ℂ) * I) ≠ 0 := by
  intro h
  have hre : p.1.1 = 0 := by simpa using congrArg Complex.re h
  have him : p.1.2 = 0 := by simpa using congrArg Complex.im h
  have h2 := p.2
  rw [hre, him] at h2
  norm_num at h2

@[simp] theorem chiChar_zero (p : SO2_QStructure ℝ) : chiChar 0 p = 1 := by simp [chiChar]

@[simp] theorem chiChar_one (n : ℤ) : chiChar n 1 = 1 := by simp [chiChar]

theorem chiChar_add (a b : ℤ) (p : SO2_QStructure ℝ) :
    chiChar (a + b) p = chiChar a p * chiChar b p := by
  unfold chiChar
  exact zpow_add₀ (chiChar_base_ne_zero p) a b

theorem chiChar_mul (n : ℤ) (p q : SO2_QStructure ℝ) :
    chiChar n (p * q) = chiChar n p * chiChar n q := by
  unfold chiChar
  rw [← mul_zpow]
  congr 1
  simp only [SO2_QStructure.mul_fst, SO2_QStructure.mul_snd]
  push_cast
  linear_combination (-((p.1.2 : ℂ) * (q.1.2 : ℂ))) * Complex.I_sq

/-- `t ↦ rot t = (cos t, sin t) = exp(tW)`, the one-parameter subgroup of `SO(2,ℝ)` generated by
`W = !![0, -1; 1, 0] = iH` (`so2Matrix (rot t) = !![cos t, -sin t; sin t, cos t]`).  (`W = −iH`
until the author's ruling of 2026-09-10 negated `H`.)

@census none
-/
noncomputable def rot (t : ℝ) : SO2_QStructure ℝ :=
  ⟨(Real.cos t, Real.sin t), Real.cos_sq_add_sin_sq t⟩

theorem chiChar_rot (n : ℤ) (t : ℝ) : chiChar n (rot t) = Complex.exp ((n : ℂ) * I * t) := by
  show ((Real.cos t : ℂ) + (Real.sin t : ℂ) * I) ^ n = _
  have h : ((Real.cos t : ℂ) + (Real.sin t : ℂ) * I) = Complex.exp ((t : ℂ) * I) := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [h, ← Complex.exp_int_mul]
  congr 1
  ring

/-- `d/dt|₀ χ_n(rot t) = +i·n`: the differential of `χ_n` on the generator `W`.  (Under the
retired `R-S7-6` convention this read `−i·n`; the author's ruling of 2026-09-10 restores the
displayed character `χ_n = (ξ + iη)^n` and with it the `+`.) -/
theorem hasDerivAt_chiChar_rot (n : ℤ) :
    HasDerivAt (fun t : ℝ => chiChar n (rot t)) ((n : ℂ) * I) 0 := by
  have hfun : (fun t : ℝ => chiChar n (rot t))
      = fun t : ℝ => Complex.exp ((n : ℂ) * I * (t : ℂ)) := funext (chiChar_rot n)
  rw [hfun]
  have h : HasDerivAt (fun z : ℂ => Complex.exp ((n : ℂ) * I * z))
      (Complex.exp ((n : ℂ) * I * ((0 : ℝ) : ℂ)) * ((n : ℂ) * I)) ((0 : ℝ) : ℂ) := by
    have := ((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul ((n : ℂ) * I)).cexp
    simpa using this
  simpa using h.comp_ofReal

/-- **The differential condition holds for every `WeightData ℂ M`, given the sign convention.**
With `H|_{M_n} = n` (`H_apply`) and `χ_n'(0) = +i·n` (`hasDerivAt_chiChar_rot`), one has
`H v = (−i·χ_n'(0))·v` on `M_n`: this is what makes `HarishChandraModule.differential` satisfiable
off degree `0` under the author's ruling of 2026-09-10, and what would have failed had `H` been left
as the source displayed it **until `17fae88` (2026-09-11)** while `χ_n` stayed as displayed.

@census none
-/
theorem WeightData.differential_of_chiChar {M : Type u} [AddCommGroup M] [Module ℂ M]
    (W : WeightData ℂ M) (n : ℤ) (v : M) (hv : v ∈ W.comp n) :
    ∃ c : ℂ, HasDerivAt (fun t : ℝ => chiChar n (rot t)) c 0 ∧ W.H v = (-(I * c)) • v :=
  ⟨_, hasDerivAt_chiChar_rot n, by
    rw [W.H_apply n v hv]
    congr 1
    linear_combination (n : ℂ) * Complex.I_sq⟩

/-- `-1₂ ∈ SL₂(ℝ)`, as the point `(-1, 0)` of `SO(2)`; `so2Matrix` sends it to `!![-1, 0; 0, -1]`.

@census none
-/
def minusOnePt (E : Type u) [CommRing E] : SO2_QStructure E := ⟨(-1, 0), by ring⟩

/-! ## `RQ2-3.11` — Harish-Chandra modules -/

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The smallest `ℂ`-submodule containing `S`, stable under the three operators and under the group
action — the `(𝔤,K)`-submodule generated by `S`.

@census none
-/
def gkSpan (ops : Set (Module.End ℂ M)) (act : Set (Module.End ℂ M)) (S : Set M) :
    Submodule ℂ M :=
  sInf {N | S ⊆ (N : Set M) ∧ (∀ f ∈ ops, ∀ v ∈ N, f v ∈ N) ∧ (∀ g ∈ act, ∀ v ∈ N, g v ∈ N)}

variable (M) in
/-- **A Harish-Chandra module for `SL₂(ℝ)`** (`§3.3`, census `RQ2-3.11`).

`M` is a complex `(𝔤,K)`-module (clause `H1`): the `𝔤 = 𝔰𝔩₂`-action is the triple carried by
`weight` (`HC/Sl2.lean`), the `K = SO(2,ℝ)`-action is `rep`, the two are compatible — condition (i),
the `𝔨`-action is the differential of the `K`-action, is the field `differential`; condition (ii),
`k·(x·v) = (Ad(k)x)·(k·v)`, is entailed and stated as `HarishChandraModule.compat_generators` —
and `M_n := M[χ_n]` is exactly the `χ_n`-isotypic component (clause `H2`, the field `isotypic`).
It is **finitely generated** (clause `C1`), **admissible** — every `M_n` is finite-dimensional
(clause `C2`) — and `M = ⨁_{n ∈ ℤ} M_n` (clause `C3`, the field `weight.isInternal`).  That
`HC(𝔤,K)` is abelian (clause `C4`) is `harishChandraCat_abelian`, below.

@census    RQ2-3.11
@source    def:hcmodule
@clauses   RQ2-3.11-H1, RQ2-3.11-H2, RQ2-3.11-C1, RQ2-3.11-C2, RQ2-3.11-C3, RQ2-3.11-Hs1
@imports   none
@divergence JUSTIFIED_REFORMULATION on clauses `RQ2-3.11-H1` and `RQ2-3.11-H2`: `K` is rendered by
its real points. **Added 2026-10-03** (docstring-only `R-PROC-4` amendment of frozen S7,
coordinator ruling `R-FR-9`, final-release WP-16b, `MISMATCH-TRIAGE.md` rows #16/#17). Until then
this field opened "`none.`". The source (census r18, FA-39) takes `K = SO(2,ℂ)` and the characters
`χ_n : SO(2,ℂ) → ℂ^×`, `(ξ,η) ↦ (ξ + iη)^n`. It adds in parentheses that their restrictions to
`SO(2,ℝ)` are precisely the continuous characters of `SO(2,ℝ)`. Here `rep` is a representation of
`SO2_QStructure ℝ`, i.e. of `SO(2,ℝ)`, and `chiChar n` is `χ_n` restricted to `SO(2,ℝ)`. The
categories agree. On `M = ⨁ M[χ_n]`, an `SO(2,ℝ)`-action through the restricted `χ_n` extends
uniquely to an algebraic `SO(2,ℂ)`-action. The restriction map on characters is injective, which
is the source's own parenthetical. So the isotypic decomposition, and with it admissibility, are
the same on either reading. The Lean object, however, carries no `SO(2,ℂ)`-action, so this is a
reformulation, not a literal rendering. The divergence is old: it dates from the S7 rendering. The
census re-sync r18 only made it visible, and it was undisclosed until this amendment.

**On the sign of `χ_n` (a separate matter): the `JUSTIFIED_REFORMULATION` this row carried from
2026-09-02 to 2026-09-10 is RETIRED, not reworded.** Under the paper author's ruling of 2026-09-10
the source's displayed character `χ_n = (ξ + iη)^n` is what `chiChar` renders (on the real points),
so clause `RQ2-3.11-H2`'s "`χ_n` as displayed" is met up to the real-points reading above, and no
sign reformulation is left to justify.

**The retired disclosure, kept because a superseded reason is recorded and never deleted
(`R-PROC-2` item 7).**  It read: *`JUSTIFIED_REFORMULATION` (one sign in `χ_n`, by coordinator
ruling `R-S7-6` of 2026-09-02 — disclosed; verifier finding V-S7-5)*.  The quoted disclosure ends
there; what follows is this file's own frame, written in 2026-09-11's past tense because its subject
moved.  The ground was that the conventions the source displayed **until `17fae88` (2026-09-11)**
were inconsistent by a sign: with `H = !![0,-i;i,0]`, the parametrisation `(ξ,η) ↦ !![ξ,-η;η,ξ]`
(so `rot t = exp(tW)`, `W = !![0,-1;1,0]`, `H = iW`) and `χ_n = (ξ+iη)^n` (so `dχ_n(W) = in`), the
differential of the `K`-action **made** `H` act on `M[χ_n]` by `−n`, and `Ad(k)X = χ_{−2}(k)X`,
while the proof of `prop:XY_C_relation` and census note `AN-22` require `H|_{M_n} = +n`
(`WeightData.H_apply`).  `R-S7-6` repaired that by rendering `H` and the parametrisation verbatim
and moving the sign into the character, `chiChar n (ξ,η) = (ξ − iη)^n`.  Until 2026-09-11 this frame
read *"on the ground that the source's displayed conventions **are** inconsistent by a sign"* —
true when written, falsified by `17fae88`, superseded and not deleted (`R-PROC-2` item 7).  The
quotation itself is untouched: quoted superseded wording is a record and is never repaired.

**What the author ruled instead, and why it closes the divergence rather than moving it.**  The
inconsistency is real and is the SOURCE's; the ruling repairs it in `H` — `H ↦ −H`, with the
explicit `X` and `Y` matrices swapped — leaving `χ_n` as displayed.  Since that map is an
automorphism of `𝔰𝔩₂` (inner over `ℂ`), every relation the source displays survives verbatim, so
**no clause of `RQ2-3.10`, `RQ2-3.11` or `RQ2-3.12` is rendered against a changed statement.**  What
remains is a **source erratum in `latex/`**, booked to the author (`AN-34`, `AN-44`, `AN-46`), not
a divergence of this rendering from the source's meaning.  **That erratum is repaired.**  The
author's own `latex/` edit landed at `17fae88` (2026-09-11), so the paper's displayed matrices at
`:1559-1561` and this file's `sl2Hm`/`sl2Xm`/`sl2Ym` now **agree, entry for entry**.  Until
2026-09-11 this passage read: *"Until the author's `latex/` edit lands, the paper's displayed
matrices at `:1559-1561` and this file's disagree"* — superseded, kept because a superseded reason
is recorded and never deleted (`R-PROC-2` item 7).  The window in which they did disagree is
disclosed in `workflow/stages/S7/FREEZE.md`'s post-freeze amendment entries, not here, because it is
a property of the tree's history and not of this declaration.

**How the two `(𝔤,K)`-compatibility conditions are carried, and what the field `differential`
adds:** condition (i), that the `𝔨`-action is the differential of the
`K`-action, is **rendered by the conjunction of `weight.H_apply` (`H|_{M_n} = +n`) with the
displayed `chiChar` (`χ_n'(0) = +i·n`)** — those two already force `H v = (−i·χ_n'(0))·v` on every
`M_n`, so the field `differential` states the condition explicitly but is **entailed** by the rest
of the structure and adds no constraint to it (`WeightData.differential_of_chiChar` proves it for
*every* `WeightData ℂ M`).  The field's function is to **fix the convention**: it is the
build-breaking guard tying the sign of `chiChar` to `H_apply`, so that flipping either one alone
leaves the structure uninhabited off degree `0`.  What the 2026-09-02 repair changed was the
**sign of `chiChar`**, and what the 2026-09-10 ruling changed is the **sign of `H`** and the
labelling of `X`/`Y`; neither changed the strength of `HarishChandraModule` (verifier finding
`V-S7-D1-1`, 2026-09-02, which stands under both).  Condition (ii), the `Ad`-compatibility, is likewise entailed
and is stated as `compat_generators`, from the fields and the matrix fact `ad_so2Matrix_triple`;
the earlier prose entailment argument used `Ad(k)X = χ_2(k)X`, which is false with the source's
original `H` and the displayed `χ_n` together, and true under each of the two repairs — `R-S7-6`'s
and the author's — because `χ_n` and the matrices move together either way (`ad_so2Matrix_triple`
is the tightest guard in the tree on exactly this point: its STATEMENT does not move under the
ruling and its TRUTH requires the character and the matrices to have moved consistently).
**Non-degeneracy under the fixed convention** is exhibited, not asserted: `stdHC` (the standard
representation `F_2 = ℂ²`, `M_{±1} ≠ 0`, `X ≠ 0 ≠ Y`, `rep` the exponential of the `H`-action)
satisfies every field including `differential`, and is an object of `HC_λ` at `ℓ = 2`
(`stdHC_mem_category`); with the `H` the source displayed **until `17fae88` (2026-09-11)** and `χ_n`
as displayed, every inhabitant would have been concentrated in degree `0`.  Until 2026-09-11 this
read *"with `H` as the source displays it and `χ_n` as displayed too"* — true when written, and
false rather than merely stale once `17fae88` made the displayed `H` the ruled one, so that the
counterfactual named the very convention it was contrasting with (`R-PROC-2` item 7).
**Landed** (2026-09-11, `17fae88`): the author's
own `latex/` edit at `:1559-1561`, `:1622` and `:2440` — `latex/` is the author's alone and is
untouched by this stage, which is why it could only be waited for.  Until 2026-09-11 this read:
*"**Pending:** the author's own `latex/` edit at `:1559-1561` (and `:2440`, `:1622`)"* — superseded,
not deleted (`R-PROC-2` item 7).  The census's `RQ2-3.11-H2` note is retired in the same round as
this amendment (`workflow/census/CLAUSES.tsv`, `NOTATION.md`);
`workflow/stages/S7/DESIGN-NOTES.md` §8.5's proposed correction is **superseded** by the ruling and
is not applied.
-/
structure HarishChandraModule where
  /-- Clause `H1`/`C3`: the `𝔤`-action and the decomposition `M = ⨁_n M_n`, with `H` acting on
  `M_n` by `n`, `X` raising `n` by `2` and `Y` lowering it by `2` (`HC.WeightData`).  Standing
  clause `RQ2-3.11-Hs1` — `(𝔤,K) = (𝔰𝔩_{2,ℂ}, SO(2,ℂ))`, the complexification of the `ℚ`-rational
  pair of `RQ2-3.12` — is carried by the base field `ℂ` here and by `SO2_QStructure ℝ` in `rep`. -/
  weight : WeightData ℂ M
  /-- Clause `H1`: the `K = SO(2,ℝ)`-action. -/
  rep : Representation ℂ (SO2_QStructure ℝ) M
  /-- Clause `H2`: `M_n` **is** the `χ_n`-isotypic component `M[χ_n]`. -/
  isotypic : ∀ (n : ℤ) (v : M), v ∈ weight.comp n ↔ ∀ g, rep g v = chiChar n g • v
  /-- Clause `H1`, condition (i) of a `(𝔤,K)`-module: **the `𝔨`-action is the differential of the
  `K`-action.**  Here `𝔨_ℂ = ℂ·W` with `W = iH` (the 2026-09-10 ruling's `H = −i·W`), and
  `rot t = exp(tW)`; on `M_n` the function `t ↦ rep (rot t) v = χ_n(rot t)·v` has derivative
  `χ_n'(0)·v` at `0`, so the condition `W·v = d/dt|₀ rep(rot t) v` reads `i·H v = χ_n'(0)·v`, i.e.
  `H v = (−i·χ_n'(0))·v`, with `χ_n'(0)` the derivative of `t ↦ χ_n(rot t)` at `0`.  Stated with
  `HasDerivAt` (no junk value).  Under the author's ruling of 2026-09-10 it is satisfiable off
  degree `0` — see `WeightData.differential_of_chiChar`; with the source's original `H` and the
  displayed `χ_n` together it is not.

  **The literal sign here is load-bearing and is NOT free.**  This field flips literally from
  `(I * c) • v` to `(-(I * c)) • v` for identical CONTENT, because `c = χ_n'(0)` flips with it.
  `tools/decl-regression.sh` can see that the type moved but not which way — both readings have the
  same arity.  The discriminator is
  `workflow/analysis/sl2-amendment/probes/P3-differential-literal-shape.lean`, which offers this
  field at the post-ruling shape and exited 1 before the amendment on a type mismatch naming both
  shapes. -/
  differential : ∀ (n : ℤ) (v : M), v ∈ weight.comp n →
    ∃ c : ℂ, HasDerivAt (fun t : ℝ => chiChar n (rot t)) c 0 ∧ weight.H v = (-(I * c)) • v
  /-- Clause `C1`: `M` is finitely generated as a `(𝔤,K)`-module. -/
  fg : ∃ S : Finset M,
    gkSpan {weight.H, weight.X, weight.Y} (Set.range fun g => (rep g : Module.End ℂ M)) ↑S = ⊤
  /-- Clause `C2`: `M` is **admissible** — every isotypic component is finite-dimensional. -/
  admissible : ∀ n : ℤ, FiniteDimensional ℂ (weight.comp n)

/-- `-1₂` acts on `M` by `(-1)^{ℓ-1}` — the central-character condition of `RQ2-3.03` (clause
`RQ2-3.03-C6`); omitting it would enlarge the category.

@census none
-/
def HarishChandraModule.centralCharacter (Hm : HarishChandraModule M) (ℓ : ℕ) : Prop :=
  ∀ v : M, Hm.rep (minusOnePt ℝ) v = ((-1 : ℂ) ^ ((ℓ : ℤ) - 1)) • v

/-! ### Projections of `HarishChandraModule`

Each field is re-exported, so that every clause it carries is projected by a named declaration
(`rqaudit liveness`).
-/

theorem HarishChandraModule.isotypic' (Hm : HarishChandraModule M) (n : ℤ) (v : M) :
    v ∈ Hm.weight.comp n ↔ ∀ g, Hm.rep g v = chiChar n g • v :=
  Hm.isotypic n v

theorem HarishChandraModule.differential' (Hm : HarishChandraModule M) (n : ℤ) (v : M)
    (hv : v ∈ Hm.weight.comp n) :
    ∃ c : ℂ, HasDerivAt (fun t : ℝ => chiChar n (rot t)) c 0 ∧ Hm.weight.H v = (-(I * c)) • v :=
  Hm.differential n v hv

theorem HarishChandraModule.fg' (Hm : HarishChandraModule M) :
    ∃ S : Finset M,
      gkSpan {Hm.weight.H, Hm.weight.X, Hm.weight.Y}
        (Set.range fun g => (Hm.rep g : Module.End ℂ M)) ↑S = ⊤ :=
  Hm.fg

theorem HarishChandraModule.admissible' (Hm : HarishChandraModule M) (n : ℤ) :
    FiniteDimensional ℂ (Hm.weight.comp n) :=
  Hm.admissible n

/-! ### Condition (ii) of a `(𝔤,K)`-module: `k·(x·v) = (Ad(k)x)·(k·v)` — entailed, and stated -/

/-! ### `Ad(k)` on the triple, and condition (ii) — the two G2 statements of `RQ2-3.11` -/

/-- `(ξ - iη)(ξ + iη) = 1` on `SO(2,ℝ)`: the two candidate characters at `n = 1` are inverse to
each other.

@census none
-/
theorem chiChar_base_mul (g : SO2_QStructure ℝ) :
    ((g.1.1 : ℂ) - (g.1.2 : ℂ) * I) * ((g.1.1 : ℂ) + (g.1.2 : ℂ) * I) = 1 := by
  have h := g.2
  have h2 : ((g.1.1 : ℂ)) ^ 2 + ((g.1.2 : ℂ)) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h
  linear_combination h2 - ((g.1.2 : ℂ)) ^ 2 * Complex.I_sq

theorem chiChar_two (g : SO2_QStructure ℝ) :
    chiChar 2 g = ((g.1.1 : ℂ) + (g.1.2 : ℂ) * I) ^ 2 := by
  show ((g.1.1 : ℂ) + (g.1.2 : ℂ) * I) ^ (2 : ℤ) = _
  rw [zpow_two, sq]

theorem chiChar_neg_two (g : SO2_QStructure ℝ) :
    chiChar (-2) g = ((g.1.1 : ℂ) - (g.1.2 : ℂ) * I) ^ 2 := by
  -- `chiChar_base_mul` is BYTE-UNCHANGED by this amendment and still discharges this proof;
  -- one `mul_comm` is all the renormalization costs here.  Its statement
  -- `(ξ − iη)(ξ + iη) = 1` is symmetric in the two candidate characters.
  have h : (((g.1.1 : ℂ) + (g.1.2 : ℂ) * I) ^ 2) * (((g.1.1 : ℂ) - (g.1.2 : ℂ) * I) ^ 2) = 1 := by
    rw [← mul_pow, mul_comm, chiChar_base_mul, one_pow]
  show ((g.1.1 : ℂ) + (g.1.2 : ℂ) * I) ^ (-2 : ℤ) = _
  rw [zpow_neg, zpow_two, ← sq]
  exact inv_eq_of_mul_eq_one_right h

theorem so2Matrix_map_eq (g : SO2_QStructure ℝ) :
    (so2Matrix g).map ((↑) : ℝ → ℂ) = !![(g.1.1 : ℂ), -(g.1.2 : ℂ); (g.1.2 : ℂ), (g.1.1 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [so2Matrix]

/-- `Ad(k)` on the classical triple, for `k = so2Matrix g ∈ SO(2,ℝ)` read as a complex matrix:
`k H k⁻¹ = H`, `k X k⁻¹ = χ_2(k) X`, `k Y k⁻¹ = χ_{−2}(k) Y` — written without inverses as
`k·H = H·k`, `k·X = χ_2(k)·(X·k)`, `k·Y = χ_{−2}(k)·(Y·k)`.  (With the PRE-RULING matrices — the
ones the source displayed until `17fae88` (2026-09-11) — taken with the displayed `χ_n`, the second
would have read `χ_{−2}`, verifier probes `probes-python.log`; under `R-S7-6` it was `χ_2`, and
it is `χ_2` again under the author's ruling of 2026-09-10 that supersedes it — the ruling swaps the
`X`/`Y` matrices and leaves `χ_n` displayed, and `χ^new_n = χ^old_{−n}`, so this statement does not
move.  That is what makes `X : M_n → M_{n+2}` compatible with the `K`-action.)

@census none
-/
theorem ad_so2Matrix_triple (g : SO2_QStructure ℝ) :
    (so2Matrix g).map ((↑) : ℝ → ℂ) * sl2Hm = sl2Hm * (so2Matrix g).map ((↑) : ℝ → ℂ)
      ∧ (so2Matrix g).map ((↑) : ℝ → ℂ) * sl2Xm
          = chiChar 2 g • (sl2Xm * (so2Matrix g).map ((↑) : ℝ → ℂ))
      ∧ (so2Matrix g).map ((↑) : ℝ → ℂ) * sl2Ym
          = chiChar (-2) g • (sl2Ym * (so2Matrix g).map ((↑) : ℝ → ℂ)) := by
  set a : ℂ := (g.1.1 : ℂ)
  set b : ℂ := (g.1.2 : ℂ)
  have hK := so2Matrix_map_eq g
  have hKX : (!![a, -b; b, a] : Matrix (Fin 2) (Fin 2) ℂ) * sl2Xm = (a + b * I) • sl2Xm := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sl2Xm, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring_nf
    all_goals (try rw [Complex.I_sq])
    all_goals ring
  have hXK : sl2Xm * (!![a, -b; b, a] : Matrix (Fin 2) (Fin 2) ℂ) = (a - b * I) • sl2Xm := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sl2Xm, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring_nf
    all_goals (try rw [Complex.I_sq])
    all_goals ring
  have hKY : (!![a, -b; b, a] : Matrix (Fin 2) (Fin 2) ℂ) * sl2Ym = (a - b * I) • sl2Ym := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sl2Ym, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring_nf
    all_goals (try rw [Complex.I_sq])
    all_goals ring
  have hYK : sl2Ym * (!![a, -b; b, a] : Matrix (Fin 2) (Fin 2) ℂ) = (a + b * I) • sl2Ym := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sl2Ym, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring_nf
    all_goals (try rw [Complex.I_sq])
    all_goals ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hK]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2Hm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · rw [hK, hKX, hXK, chiChar_two, smul_smul]
    congr 1
    linear_combination (-(a + b * I)) * chiChar_base_mul g
  · rw [hK, hKY, hYK, chiChar_neg_two, smul_smul]
    congr 1
    linear_combination (-(a - b * I)) * chiChar_base_mul g

/-- Condition (ii) of a `(𝔤,K)`-module on the generators of `𝔤`: for every `k ∈ SO(2,ℝ)` and
`v ∈ M`, `k·(H v) = H (k v)`, `k·(X v) = χ_2(k)·X(k v)`, `k·(Y v) = χ_{−2}(k)·Y(k v)` — i.e.
`k·(x·v) = (Ad(k)x)·(k·v)` for `x ∈ {H, X, Y}`, with `Ad(k)` given by `ad_so2Matrix_triple`.

**Entailed, not assumed** (which is why it is a theorem and not a field): for `v ∈ M_n`,
`X v ∈ M_{n+2}` (`X_mem`), so `k·(X v) = χ_{n+2}(k)·X v = χ_2(k)·χ_n(k)·X v = χ_2(k)·X(k v)` by
`isotypic` and `chiChar_add`; likewise for `Y` with `−2` and for `H` with `0`; and the identities
extend from the `M_n` to `M` by `isInternal`.  Stated at G2 so that the entailment is a G4
obligation rather than a prose remark (the pre-repair prose argument was wrong under the sign the
source displayed until `17fae88`, 2026-09-11 — verifier finding V-S7-5).

@census none
-/
theorem HarishChandraModule.compat_generators (Hm : HarishChandraModule M)
    (g : SO2_QStructure ℝ) (v : M) :
    Hm.rep g (Hm.weight.H v) = Hm.weight.H (Hm.rep g v)
      ∧ Hm.rep g (Hm.weight.X v) = chiChar 2 g • Hm.weight.X (Hm.rep g v)
      ∧ Hm.rep g (Hm.weight.Y v) = chiChar (-2) g • Hm.weight.Y (Hm.rep g v) := by
  set P : M → Prop := fun w =>
    Hm.rep g (Hm.weight.H w) = Hm.weight.H (Hm.rep g w)
      ∧ Hm.rep g (Hm.weight.X w) = chiChar 2 g • Hm.weight.X (Hm.rep g w)
      ∧ Hm.rep g (Hm.weight.Y w) = chiChar (-2) g • Hm.weight.Y (Hm.rep g w) with hP
  have hcomp : ∀ (n : ℤ), ∀ w ∈ Hm.weight.comp n, P w := by
    intro n w hw
    have hrep : Hm.rep g w = chiChar n g • w := (Hm.isotypic n w).mp hw g
    have hH : Hm.weight.H w = (n : ℂ) • w := Hm.weight.H_apply n w hw
    have hXm : Hm.weight.X w ∈ Hm.weight.comp (n + 2) := Hm.weight.X_mem n w hw
    have hYm : Hm.weight.Y w ∈ Hm.weight.comp (n - 2) := Hm.weight.Y_mem n w hw
    refine ⟨?_, ?_, ?_⟩
    · rw [hH, map_smul, hrep, map_smul, hH, smul_comm]
    · rw [(Hm.isotypic (n + 2) _).mp hXm g, hrep, map_smul, smul_smul, add_comm n 2,
        chiChar_add]
    · rw [(Hm.isotypic (n - 2) _).mp hYm g, hrep, map_smul, smul_smul,
        show n - 2 = -2 + n by ring, chiChar_add]
  have hzero : P 0 := by
    refine ⟨by simp, by simp, by simp⟩
  have hadd : ∀ w z, P w → P z → P (w + z) := by
    rintro w z ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [map_add, map_add, map_add, h1, k1, map_add]
    · rw [map_add, map_add, h2, k2, map_add, map_add, smul_add]
    · rw [map_add, map_add, h3, k3, map_add, map_add, smul_add]
  have htop : (⨆ n : ℤ, Hm.weight.comp n) = ⊤ :=
    Hm.weight.isInternal.submodule_iSup_eq_top
  have hv : v ∈ ⨆ n : ℤ, Hm.weight.comp n := by rw [htop]; trivial
  induction hv using Submodule.iSup_induction' with
  | mem n w hw => exact hcomp n w hw
  | zero => exact hzero
  | add w z _ _ hw hz => exact hadd w z hw hz

/-! ## The category `HC(𝔤,K)` -/

/-- An object of `HC(𝔤,K)`: a complex vector space together with its Harish-Chandra structure.

@census none
-/
structure HCObj : Type (u + 1) where
  /-- the underlying complex vector space -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  /-- its Harish-Chandra structure -/
  str : HarishChandraModule carrier

attribute [instance] HCObj.addCommGroup HCObj.module

/-- A morphism of `HC(𝔤,K)`: a `ℂ`-linear map commuting with `H`, `X`, `Y` and with the
`SO(2,ℝ)`-action.

@census none
-/
structure HCHom (A B : HCObj.{u}) where
  /-- the underlying `ℂ`-linear map -/
  toLinearMap : A.carrier →ₗ[ℂ] B.carrier
  /-- it commutes with `H` -/
  map_H : ∀ v, toLinearMap (A.str.weight.H v) = B.str.weight.H (toLinearMap v)
  /-- it commutes with `X` -/
  map_X : ∀ v, toLinearMap (A.str.weight.X v) = B.str.weight.X (toLinearMap v)
  /-- it commutes with `Y` -/
  map_Y : ∀ v, toLinearMap (A.str.weight.Y v) = B.str.weight.Y (toLinearMap v)
  /-- it is `SO(2,ℝ)`-equivariant -/
  map_rep : ∀ g v, toLinearMap (A.str.rep g v) = B.str.rep g (toLinearMap v)

namespace HCHom

@[ext] theorem hom_ext {A B : HCObj.{u}} {f g : HCHom A B}
    (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f; cases g; simp_all

end HCHom

/-- `HC(𝔤,K)`, the category of Harish-Chandra modules over `ℂ` (clause `RQ2-3.11-C4`). -/
instance : CategoryTheory.Category HCObj.{u} where
  Hom A B := HCHom A B
  id A := ⟨LinearMap.id, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
  comp f g :=
    ⟨g.toLinearMap.comp f.toLinearMap,
      fun v => by simp [f.map_H, g.map_H],
      fun v => by simp [f.map_X, g.map_X],
      fun v => by simp [f.map_Y, g.map_Y],
      fun g' v => by simp [f.map_rep, g.map_rep]⟩
  id_comp _ := by apply HCHom.hom_ext; rfl
  comp_id _ := by apply HCHom.hom_ext; rfl
  assoc _ _ _ := by apply HCHom.hom_ext; rfl

open Real in
/-- For `n ≠ 0` the character `χ_n` is **non-trivial**: `SO(2,ℝ)` has a point where it takes the
value `i`.  This is what makes `HarishChandraModule.isotypic` a real condition rather than a
convention — without it the `M_n` could not be pinned down by the `K`-action.

@census none
-/
theorem exists_chiChar_ne_one {n : ℤ} (hn : n ≠ 0) :
    ∃ g : SO2_QStructure ℝ, chiChar n g ≠ 1 := by
  have hnR : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hnC : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  refine ⟨rot (Real.pi / (2 * (n : ℝ))), ?_⟩
  rw [chiChar_rot]
  have h : (n : ℂ) * I * (((Real.pi / (2 * (n : ℝ))) : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * I := by
    push_cast
    field_simp
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  intro h1
  have := congrArg Complex.im h1
  simp at this

/-- If `χ_m(g)·x = x` for every `g` and some `m ≠ 0`, then `x = 0`.

@census none
-/
theorem eq_zero_of_forall_chiChar_mul_eq {m : ℤ} (hm : m ≠ 0) {x : ℂ}
    (h : ∀ g, chiChar m g * x = x) : x = 0 := by
  obtain ⟨g, hg⟩ := exists_chiChar_ne_one hm
  have : (chiChar m g - 1) * x = 0 := by rw [sub_mul, one_mul, h g, sub_self]
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hg
  · exact h1

/-! ## `RQ2-3.11-C4` — the abelian structure of `HC(𝔤,K)`

The construction of the `Abelian` instance whose existence clause `RQ2-3.11-C4` asserts.  The one
non-formal ingredient is `WeightData.exists_finite_generating_set` (`HC/Noetherian.lean`): a
`(𝔤,K)`-submodule of a finitely generated admissible module is again finitely generated, which is
what lets `ker f` be an **object** of `HC(𝔤,K)` and not merely a `(𝔤,K)`-module.  Everything else
is the `ModuleCat` pattern (`Mathlib/Algebra/Category/ModuleCat/Abelian.lean`): a preadditive
category with kernels, cokernels and finite products in which every mono is a kernel and every
epi is a cokernel.
-/

/-! ### `gkSpan`, and homogeneity as the `K`-half of a `(𝔤,K)`-submodule -/

/-- To be `⊤`, it suffices for a `(𝔤,K)`-stable submodule containing the generators to be so.

@census none
-/
theorem eq_top_of_gkSpan_eq_top {ops act : Set (Module.End ℂ M)} {S : Set M} {P : Submodule ℂ M}
    (h : gkSpan ops act S = ⊤) (hS : S ⊆ (P : Set M))
    (hops : ∀ f ∈ ops, ∀ v ∈ P, f v ∈ P) (hact : ∀ g ∈ act, ∀ v ∈ P, g v ∈ P) : P = ⊤ := by
  have hle : (⊤ : Submodule ℂ M) ≤ P := h ▸ sInf_le ⟨hS, hops, hact⟩
  exact top_le_iff.mp hle

/-- The converse packaging: `gkSpan` is `⊤` exactly when every stable submodule containing the
generators is.

@census none
-/
theorem gkSpan_eq_top {ops act : Set (Module.End ℂ M)} {S : Set M}
    (h : ∀ P : Submodule ℂ M, S ⊆ (P : Set M) → (∀ f ∈ ops, ∀ v ∈ P, f v ∈ P) →
      (∀ g ∈ act, ∀ v ∈ P, g v ∈ P) → P = ⊤) :
    gkSpan ops act S = ⊤ :=
  le_antisymm le_top (le_sInf fun _ hQ => (h _ hQ.1 hQ.2.1 hQ.2.2) ▸ le_rfl)

theorem opStable_iff_forall_mem {W : WeightData ℂ M} {P : Submodule ℂ M} :
    W.OpStable P ↔ ∀ f ∈ ({W.H, W.X, W.Y} : Set (Module.End ℂ M)), ∀ v ∈ P, f v ∈ P := by
  constructor
  · rintro ⟨h1, h2, h3⟩ f hf v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl
    exacts [h1 v hv, h2 v hv, h3 v hv]
  · intro h
    exact ⟨h _ (by simp), h _ (by simp), h _ (by simp)⟩

/-- **A homogeneous submodule is automatically `K`-stable**, because `rep g` acts on `M_n` by the
scalar `χ_n(g)`.  This is what lets the whole finiteness argument (`HC/Noetherian.lean`) be about
the `𝔤`-action and the grading alone.

@census none
-/
theorem HarishChandraModule.rep_mem_of_isHomog (Hm : HarishChandraModule M) {N : Submodule ℂ M}
    (hhom : Hm.weight.IsHomog N) (g : SO2_QStructure ℝ) (v : M) (hv : v ∈ N) :
    Hm.rep g v ∈ N := by
  obtain ⟨s, -, hsum⟩ := Hm.weight.exists_sum_proj v
  have hexp : Hm.rep g v = ∑ n ∈ s, Hm.rep g (Hm.weight.proj n v) := by
    conv_lhs => rw [← hsum]
    rw [map_sum]
  rw [hexp]
  refine sum_mem fun n _ => ?_
  rw [(Hm.isotypic n _).mp (Hm.weight.proj_mem n v) g]
  exact Submodule.smul_mem _ _ (hhom n v hv)

/-- The `K`-action restricted to a homogeneous submodule.

@census none
-/
noncomputable def HarishChandraModule.subRep (Hm : HarishChandraModule M) {N : Submodule ℂ M}
    (hhom : Hm.weight.IsHomog N) : Representation ℂ (SO2_QStructure ℝ) N where
  toFun g := (Hm.rep g).restrict (fun v hv => Hm.rep_mem_of_isHomog hhom g v hv)
  map_one' := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    show Hm.rep 1 (v : M) = (v : M)
    rw [map_one]; rfl
  map_mul' g h := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    show Hm.rep (g * h) (v : M) = Hm.rep g (Hm.rep h (v : M))
    rw [map_mul]; rfl

@[simp] theorem HarishChandraModule.subRep_coe (Hm : HarishChandraModule M) {N : Submodule ℂ M}
    (hhom : Hm.weight.IsHomog N) (g : SO2_QStructure ℝ) (v : N) :
    ((Hm.subRep hhom g v : N) : M) = Hm.rep g (v : M) := rfl

/-- The `K`-action descended to the quotient by a homogeneous submodule.

@census none
-/
noncomputable def HarishChandraModule.quotRep (Hm : HarishChandraModule M) {N : Submodule ℂ M}
    (hhom : Hm.weight.IsHomog N) : Representation ℂ (SO2_QStructure ℝ) (M ⧸ N) where
  toFun g := N.mapQ N (Hm.rep g) (fun v hv => Hm.rep_mem_of_isHomog hhom g v hv)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
    show (Submodule.Quotient.mk (Hm.rep 1 v) : M ⧸ N) = _
    rw [map_one]; rfl
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
    show (Submodule.Quotient.mk (Hm.rep (g * h) v) : M ⧸ N) = _
    rw [map_mul]; rfl

@[simp] theorem HarishChandraModule.quotRep_mk (Hm : HarishChandraModule M) {N : Submodule ℂ M}
    (hhom : Hm.weight.IsHomog N) (g : SO2_QStructure ℝ) (v : M) :
    Hm.quotRep hhom g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (Hm.rep g v) := rfl

/-- Clause `RQ2-3.11-C1` re-read: a Harish-Chandra module is generated by finitely many **weight
vectors**, and a homogeneous stable submodule containing them is everything.  This is the shape
`WeightData.exists_finite_generating_set` consumes.

@census none
-/
theorem HarishChandraModule.exists_homogeneous_generators (Hm : HarishChandraModule M) :
    ∃ T : Finset M, (∀ v ∈ T, ∃ n : ℤ, v ∈ Hm.weight.comp n) ∧
      ∀ P : Submodule ℂ M, (↑T : Set M) ⊆ (P : Set M) → Hm.weight.OpStable P →
        Hm.weight.IsHomog P → P = ⊤ := by
  classical
  obtain ⟨S, hS⟩ := Hm.fg
  choose sup hzero hsum using Hm.weight.exists_sum_proj
  refine ⟨S.biUnion (fun s => (sup s).image (fun n => Hm.weight.proj n s)), ?_, ?_⟩
  · intro v hv
    simp only [Finset.mem_biUnion, Finset.mem_image] at hv
    obtain ⟨s, -, n, -, rfl⟩ := hv
    exact ⟨n, Hm.weight.proj_mem n s⟩
  · intro P hTP hst hhom
    refine eq_top_of_gkSpan_eq_top hS ?_ (opStable_iff_forall_mem.mp hst) ?_
    · intro s hs
      simp only [Finset.mem_coe] at hs
      rw [SetLike.mem_coe, ← hsum s]
      refine sum_mem fun n hn => ?_
      refine hTP ?_
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.coe_image,
        Set.mem_image, exists_prop]
      exact ⟨s, hs, n, hn, rfl⟩
    · rintro f ⟨g0, rfl⟩ v hv
      exact Hm.rep_mem_of_isHomog hhom g0 v hv

/-- The finiteness `RQ2-3.11-C4` turns on: a homogeneous `H`/`X`/`Y`-stable submodule of a
Harish-Chandra module is itself finitely generated as a `(𝔤,K)`-module.  `HC/Noetherian.lean`'s
theorem, transported across `N.subtype`.

@census none
-/
theorem HarishChandraModule.fg_sub (Hm : HarishChandraModule M) {N : Submodule ℂ M}
    (hst : Hm.weight.OpStable N) (hhom : Hm.weight.IsHomog N) :
    ∃ S : Finset N,
      gkSpan {(Hm.weight.sub hst hhom).H, (Hm.weight.sub hst hhom).X,
        (Hm.weight.sub hst hhom).Y}
        (Set.range fun g => ((Hm.subRep hhom g) : Module.End ℂ N)) ↑S = ⊤ := by
  classical
  obtain ⟨T, hTw, hTgen⟩ := Hm.exists_homogeneous_generators
  obtain ⟨S, hSN, hSgen⟩ :=
    WeightData.exists_finite_generating_set Hm.weight Hm.admissible T hTw hTgen N hst hhom
  have hmem : ∀ x : {a : M // a ∈ S}, (x : M) ∈ N := fun x => hSN x.2
  refine ⟨S.attach.image (fun x : {a : M // a ∈ S} => (⟨(x : M), hmem x⟩ : N)),
    gkSpan_eq_top ?_⟩
  intro Q hQS hQops hQact
  have hPle : N ≤ Q.map N.subtype := by
    refine hSgen (Q.map N.subtype) ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe] at hx
      refine ⟨⟨x, hSN (by simpa using hx)⟩, ?_, rfl⟩
      refine hQS ?_
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
    · refine ⟨?_, ?_, ?_⟩ <;> rintro v ⟨w, hw, rfl⟩
      · exact ⟨(Hm.weight.sub hst hhom).H w, hQops _ (by simp) w hw, rfl⟩
      · exact ⟨(Hm.weight.sub hst hhom).X w, hQops _ (by simp) w hw, rfl⟩
      · exact ⟨(Hm.weight.sub hst hhom).Y w, hQops _ (by simp) w hw, rfl⟩
  rw [eq_top_iff]
  intro x _
  have hx : (x : M) ∈ Q.map N.subtype := hPle x.2
  obtain ⟨y, hy, hxy⟩ := hx
  have : y = x := Subtype.ext hxy
  rwa [← this]

/-! ### The `χ_n` separate points, so isotypy forces homogeneity -/

theorem chiChar_ne_zero (n : ℤ) (g : SO2_QStructure ℝ) : chiChar n g ≠ 0 :=
  zpow_ne_zero _ (chiChar_base_ne_zero g)

/-- **Isotypy forces homogeneity.**  If every `M_n` lies inside the `χ_n`-isotypic space of a
representation, then the two coincide: a vector on which `K` acts by `χ_n` is already in `M_n`.

The proof is the one-character separation `exists_chiChar_ne_one`, applied to the homogeneous
components of `v`: `rep g` preserves each `M_m`, so it commutes with the projections
(`WeightData.proj_comm_of_graded`), and comparing `χ_m(g)·v_m` with `χ_n(g)·v_m` kills `v_m` for
`m ≠ n`.  No Vandermonde system is needed, because the components are compared one at a time.

@census none
-/
theorem isotypic_of_forward {W : WeightData ℂ M}
    (rep : Representation ℂ (SO2_QStructure ℝ) M)
    (hfwd : ∀ (n : ℤ) (v : M), v ∈ W.comp n → ∀ g, rep g v = chiChar n g • v)
    (n : ℤ) (v : M) (h : ∀ g, rep g v = chiChar n g • v) : v ∈ W.comp n := by
  have hgr : ∀ (g : SO2_QStructure ℝ) (m : ℤ) (w : M), w ∈ W.comp m →
      (rep g : Module.End ℂ M) w ∈ W.comp m := by
    intro g m w hw
    rw [hfwd m w hw g]
    exact Submodule.smul_mem _ _ hw
  obtain ⟨s, hzero, hsum⟩ := W.exists_sum_proj v
  have hkey : ∀ m : ℤ, m ≠ n → W.proj m v = 0 := by
    intro m hmn
    have hcomm : ∀ g : SO2_QStructure ℝ,
        chiChar m g • W.proj m v = chiChar n g • W.proj m v := by
      intro g
      have h1 : W.proj m ((rep g : Module.End ℂ M) v)
          = (rep g : Module.End ℂ M) (W.proj m v) :=
        W.proj_comm_of_graded _ (hgr g) m v
      have h2 : (rep g : Module.End ℂ M) (W.proj m v) = chiChar m g • W.proj m v :=
        hfwd m _ (W.proj_mem m v) g
      have h3 : W.proj m ((rep g : Module.End ℂ M) v) = chiChar n g • W.proj m v := by
        rw [show (rep g : Module.End ℂ M) v = chiChar n g • v from h g, map_smul]
      rw [← h2, ← h1]
      exact h3
    obtain ⟨g, hg⟩ := exists_chiChar_ne_one (sub_ne_zero.mpr hmn)
    have hne : chiChar m g - chiChar n g ≠ 0 := by
      intro hz
      apply hg
      have hmn' : chiChar m g = chiChar (m - n) g * chiChar n g := by
        rw [← chiChar_add]
        congr 1
        ring
      rw [hmn'] at hz
      have h0 : (chiChar (m - n) g - 1) * chiChar n g = 0 := by
        rw [sub_mul, one_mul]; exact hz
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact sub_eq_zero.mp h1
      · exact absurd h1 (chiChar_ne_zero n g)
    have := hcomm g
    rw [← sub_eq_zero, ← sub_smul] at this
    exact (smul_eq_zero.mp this).resolve_left hne
  have hv2 : v = W.proj n v := by
    conv_lhs => rw [← hsum]
    exact Finset.sum_eq_single n (fun m _ hmn => hkey m hmn) (fun hn => hzero n hn)
  rw [hv2]
  exact W.proj_mem n v

/-! ### Sub-objects and quotient objects of `HC(𝔤,K)` -/

/-- The Harish-Chandra structure on a homogeneous, `H`/`X`/`Y`-stable submodule.  The `fg` field is
`HarishChandraModule.fg_sub`, i.e. `HC/Noetherian.lean`'s theorem; `admissible` is finite
dimensionality of a subspace of `M_n`; `differential` is free for every `WeightData ℂ`
(`WeightData.differential_of_chiChar`).

@census none
-/
noncomputable def HarishChandraModule.sub (Hm : HarishChandraModule M) {N : Submodule ℂ M}
    (hst : Hm.weight.OpStable N) (hhom : Hm.weight.IsHomog N) : HarishChandraModule N where
  weight := Hm.weight.sub hst hhom
  rep := Hm.subRep hhom
  isotypic n v := by
    constructor
    · intro hv g
      refine Subtype.ext ?_
      show Hm.rep g (v : M) = chiChar n g • (v : M)
      exact (Hm.isotypic n (v : M)).mp hv g
    · intro h
      refine isotypic_of_forward (W := Hm.weight.sub hst hhom) _ ?_ n v h
      intro m w hw g
      refine Subtype.ext ?_
      show Hm.rep g (w : M) = chiChar m g • (w : M)
      exact (Hm.isotypic m (w : M)).mp hw g
  differential n v hv := (Hm.weight.sub hst hhom).differential_of_chiChar n v hv
  fg := Hm.fg_sub hst hhom
  admissible n := by
    haveI := Hm.admissible n
    let f : ((Hm.weight.sub hst hhom).comp n) →ₗ[ℂ] (Hm.weight.comp n) :=
      { toFun := fun v => ⟨((v : N) : M), v.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective f := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : (Hm.weight.comp n) => (z : M)) hxy))
    exact FiniteDimensional.of_injective f hinj

/-- The Harish-Chandra structure on the quotient by a homogeneous, `H`/`X`/`Y`-stable submodule.

@census none
-/
noncomputable def HarishChandraModule.quot (Hm : HarishChandraModule M) {N : Submodule ℂ M}
    (hst : Hm.weight.OpStable N) (hhom : Hm.weight.IsHomog N) : HarishChandraModule (M ⧸ N) where
  weight := Hm.weight.quot hst hhom
  rep := Hm.quotRep hhom
  isotypic n v := by
    have hfwd : ∀ (m : ℤ) (w : M ⧸ N), w ∈ (Hm.weight.quot hst hhom).comp m →
        ∀ g, (Hm.quotRep hhom g) w = chiChar m g • w := by
      rintro m w ⟨a, ha, rfl⟩ g
      show (Submodule.Quotient.mk (Hm.rep g a) : M ⧸ N) = chiChar m g • Submodule.Quotient.mk a
      rw [(Hm.isotypic m a).mp ha g]
      rfl
    exact ⟨fun hv g => hfwd n v hv g,
      fun h => isotypic_of_forward (W := Hm.weight.quot hst hhom) _ hfwd n v h⟩
  differential n v hv := (Hm.weight.quot hst hhom).differential_of_chiChar n v hv
  fg := by
    classical
    obtain ⟨S, hS⟩ := Hm.fg
    refine ⟨S.image N.mkQ, gkSpan_eq_top fun P hSP hops hact => ?_⟩
    have hcomap : (Submodule.comap N.mkQ P) = ⊤ := by
      refine eq_top_of_gkSpan_eq_top hS ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_coe] at hx
        refine hSP ?_
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
        exact ⟨x, hx, rfl⟩
      · rintro f hf v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
        rcases hf with rfl | rfl | rfl
        · exact hops (Hm.weight.quot hst hhom).H (by simp) _ hv
        · exact hops (Hm.weight.quot hst hhom).X (by simp) _ hv
        · exact hops (Hm.weight.quot hst hhom).Y (by simp) _ hv
      · rintro f ⟨g, rfl⟩ v hv
        exact hact (Hm.quotRep hhom g) ⟨g, rfl⟩ _ hv
    rw [eq_top_iff]
    intro x _
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
    have : v ∈ Submodule.comap N.mkQ P := by rw [hcomap]; trivial
    exact this
  admissible n := by
    haveI := Hm.admissible n
    have h1 : (Hm.weight.comp n).FG := (Module.Finite.iff_fg (N := Hm.weight.comp n)).mp
      inferInstance
    exact (Module.Finite.iff_fg (N := (Hm.weight.quot hst hhom).comp n)).mpr (h1.map N.mkQ)

/-! ### Binary products and the zero object -/

section Prod

variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]

theorem prodMap_inl (f : Module.End ℂ M₁) (f' : Module.End ℂ M₂) (v : M₁) :
    (f.prodMap f') (LinearMap.inl ℂ M₁ M₂ v) = LinearMap.inl ℂ M₁ M₂ (f v) := by
  refine Prod.ext rfl ?_
  simp

theorem prodMap_inr (f : Module.End ℂ M₁) (f' : Module.End ℂ M₂) (v : M₂) :
    (f.prodMap f') (LinearMap.inr ℂ M₁ M₂ v) = LinearMap.inr ℂ M₁ M₂ (f' v) := by
  refine Prod.ext ?_ rfl
  simp

/-- The `K`-action on a binary product.

@census none
-/
noncomputable def HarishChandraModule.prodRep (H₁ : HarishChandraModule M₁)
    (H₂ : HarishChandraModule M₂) : Representation ℂ (SO2_QStructure ℝ) (M₁ × M₂) where
  toFun g := (H₁.rep g).prodMap (H₂.rep g)
  map_one' := by
    refine LinearMap.ext fun v => Prod.ext ?_ ?_ <;> simp
  map_mul' g h := by
    refine LinearMap.ext fun v => Prod.ext ?_ ?_ <;> simp

@[simp] theorem HarishChandraModule.prodRep_apply (H₁ : HarishChandraModule M₁)
    (H₂ : HarishChandraModule M₂) (g : SO2_QStructure ℝ) (v : M₁ × M₂) :
    H₁.prodRep H₂ g v = (H₁.rep g v.1, H₂.rep g v.2) := rfl

/-- The Harish-Chandra structure on a binary product, componentwise.

@census none
-/
noncomputable def HarishChandraModule.prod (H₁ : HarishChandraModule M₁)
    (H₂ : HarishChandraModule M₂) : HarishChandraModule (M₁ × M₂) where
  weight := WeightData.prodData H₁.weight H₂.weight
  rep := H₁.prodRep H₂
  isotypic n v := by
    have hfwd : ∀ (m : ℤ) (w : M₁ × M₂), w ∈ (WeightData.prodData H₁.weight H₂.weight).comp m →
        ∀ g, (H₁.prodRep H₂ g) w = chiChar m g • w := by
      intro m w hw g
      refine Prod.ext ?_ ?_
      · exact (H₁.isotypic m w.1).mp hw.1 g
      · exact (H₂.isotypic m w.2).mp hw.2 g
    exact ⟨fun hv g => hfwd n v hv g,
      fun h => isotypic_of_forward (W := WeightData.prodData H₁.weight H₂.weight) _ hfwd n v h⟩
  differential n v hv :=
    (WeightData.prodData H₁.weight H₂.weight).differential_of_chiChar n v hv
  fg := by
    classical
    obtain ⟨S₁, hS₁⟩ := H₁.fg
    obtain ⟨S₂, hS₂⟩ := H₂.fg
    refine ⟨S₁.image (fun a => (a, (0 : M₂))) ∪ S₂.image (fun b => ((0 : M₁), b)),
      gkSpan_eq_top fun P hSP hops hact => ?_⟩
    have h1 : (Submodule.comap (LinearMap.inl ℂ M₁ M₂) P) = ⊤ := by
      refine eq_top_of_gkSpan_eq_top hS₁ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_coe] at hx
        refine hSP ?_
        simp only [Finset.coe_union, Set.mem_union, Finset.coe_image, Set.mem_image,
          Finset.mem_coe]
        exact Or.inl ⟨x, hx, rfl⟩
      · rintro f hf v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
        rcases hf with rfl | rfl | rfl
        · rw [Submodule.mem_comap, ← prodMap_inl H₁.weight.H H₂.weight.H]
          exact hops (WeightData.prodData H₁.weight H₂.weight).H (by simp) _ hv
        · rw [Submodule.mem_comap, ← prodMap_inl H₁.weight.X H₂.weight.X]
          exact hops (WeightData.prodData H₁.weight H₂.weight).X (by simp) _ hv
        · rw [Submodule.mem_comap, ← prodMap_inl H₁.weight.Y H₂.weight.Y]
          exact hops (WeightData.prodData H₁.weight H₂.weight).Y (by simp) _ hv
      · rintro f ⟨g, rfl⟩ v hv
        rw [Submodule.mem_comap, ← prodMap_inl (H₁.rep g) (H₂.rep g)]
        exact hact (H₁.prodRep H₂ g) ⟨g, rfl⟩ _ hv
    have h2 : (Submodule.comap (LinearMap.inr ℂ M₁ M₂) P) = ⊤ := by
      refine eq_top_of_gkSpan_eq_top hS₂ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_coe] at hx
        refine hSP ?_
        simp only [Finset.coe_union, Set.mem_union, Finset.coe_image, Set.mem_image,
          Finset.mem_coe]
        exact Or.inr ⟨x, hx, rfl⟩
      · rintro f hf v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
        rcases hf with rfl | rfl | rfl
        · rw [Submodule.mem_comap, ← prodMap_inr H₁.weight.H H₂.weight.H]
          exact hops (WeightData.prodData H₁.weight H₂.weight).H (by simp) _ hv
        · rw [Submodule.mem_comap, ← prodMap_inr H₁.weight.X H₂.weight.X]
          exact hops (WeightData.prodData H₁.weight H₂.weight).X (by simp) _ hv
        · rw [Submodule.mem_comap, ← prodMap_inr H₁.weight.Y H₂.weight.Y]
          exact hops (WeightData.prodData H₁.weight H₂.weight).Y (by simp) _ hv
      · rintro f ⟨g, rfl⟩ v hv
        rw [Submodule.mem_comap, ← prodMap_inr (H₁.rep g) (H₂.rep g)]
        exact hact (H₁.prodRep H₂ g) ⟨g, rfl⟩ _ hv
    rw [eq_top_iff]
    rintro ⟨a, b⟩ _
    have ha : (a, (0 : M₂)) ∈ P := by
      have : a ∈ Submodule.comap (LinearMap.inl ℂ M₁ M₂) P := by rw [h1]; trivial
      exact this
    have hb : ((0 : M₁), b) ∈ P := by
      have : b ∈ Submodule.comap (LinearMap.inr ℂ M₁ M₂) P := by rw [h2]; trivial
      exact this
    have : ((a, b) : M₁ × M₂) = (a, (0 : M₂)) + ((0 : M₁), b) := by simp
    rw [this]
    exact add_mem ha hb
  admissible n := by
    haveI := H₁.admissible n
    haveI := H₂.admissible n
    let f : ((WeightData.prodData H₁.weight H₂.weight).comp n) →ₗ[ℂ]
        ((H₁.weight.comp n) × (H₂.weight.comp n)) :=
      { toFun := fun v => (⟨v.1.1, v.2.1⟩, ⟨v.1.2, v.2.2⟩)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective f := by
      intro x y hxy
      refine Subtype.ext (Prod.ext ?_ ?_)
      · exact congrArg (fun z => ((z.1 : M₁))) hxy
      · exact congrArg (fun z => ((z.2 : M₂))) hxy
    exact FiniteDimensional.of_injective f hinj

end Prod

/-- The **zero** Harish-Chandra module, in an arbitrary universe.

@census none
-/
noncomputable def zeroHC : HarishChandraModule PUnit.{u + 1} where
  weight := trivialWeightData ℂ PUnit.{u + 1}
  rep := 1
  isotypic n v := ⟨fun _ _ => Subsingleton.elim _ _, fun _ => by
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _⟩
  differential n v hv := (trivialWeightData ℂ PUnit.{u + 1}).differential_of_chiChar n v hv
  fg := ⟨∅, gkSpan_eq_top fun P _ _ _ => by
    rw [eq_top_iff]
    intro v _
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _⟩
  admissible n := by
    haveI : FiniteDimensional ℂ PUnit.{u + 1} :=
      ⟨⟨∅, by
        rw [eq_top_iff]
        intro v _
        rw [Subsingleton.elim v 0]
        exact Submodule.zero_mem _⟩⟩
    infer_instance


/-! ### The objects of `HC(𝔤,K)` built from the constructions above -/

/-- The sub-object of `A` carried by a homogeneous, `H`/`X`/`Y`-stable submodule.

@census none
-/
noncomputable def HCObj.sub (A : HCObj.{u}) {N : Submodule ℂ A.carrier}
    (hst : A.str.weight.OpStable N) (hhom : A.str.weight.IsHomog N) : HCObj.{u} :=
  ⟨N, A.str.sub hst hhom⟩

/-- The quotient object of `A` by a homogeneous, `H`/`X`/`Y`-stable submodule.

@census none
-/
noncomputable def HCObj.quot (A : HCObj.{u}) {N : Submodule ℂ A.carrier}
    (hst : A.str.weight.OpStable N) (hhom : A.str.weight.IsHomog N) : HCObj.{u} :=
  ⟨A.carrier ⧸ N, A.str.quot hst hhom⟩

/-- The product object.

@census none
-/
noncomputable def HCObj.prod (A B : HCObj.{u}) : HCObj.{u} :=
  ⟨A.carrier × B.carrier, A.str.prod B.str⟩

/-- The zero object, in the same universe as any other object.

@census none
-/
noncomputable def HCObj.zero : HCObj.{u} := ⟨PUnit.{u + 1}, zeroHC⟩

/-! ### Morphisms: what they do to the grading, and the two cancellation lemmas -/

namespace HCHom

variable {A B T : HCObj.{u}}

theorem toLinearMap_injective : Function.Injective (HCHom.toLinearMap : HCHom A B → _) :=
  fun _ _ h => hom_ext h

/-- A morphism preserves the grading: `f (A_n) ⊆ B_n`.  Immediate from the `isotypic` **iff** and
`SO(2)`-equivariance — no character theory.

@census none
-/
theorem map_comp_mem (f : HCHom A B) (n : ℤ) (v : A.carrier) (hv : v ∈ A.str.weight.comp n) :
    f.toLinearMap v ∈ B.str.weight.comp n := by
  refine (B.str.isotypic n _).mpr fun g => ?_
  rw [← f.map_rep, (A.str.isotypic n v).mp hv g, map_smul]

/-- **`ker f` is homogeneous** — the gradedness the abelian structure needs, and it costs nothing:
`f` preserves the grading and `B = ⨁ B_n` is a *direct* sum, so a relation `∑ f(v_n) = 0` with
`f(v_n) ∈ B_n` forces every term to vanish.  This is why the hand-over memo's step 1 (Vandermonde
character separation) is not needed.

@census none
-/
theorem isHomog_ker (f : HCHom A B) :
    A.str.weight.IsHomog (LinearMap.ker f.toLinearMap) := by
  intro n v hv
  rw [LinearMap.mem_ker] at hv ⊢
  have h := WeightData.proj_comm_of_map A.str.weight B.str.weight f.toLinearMap
    (fun m w hw => f.map_comp_mem m w hw) n v
  rw [hv, map_zero] at h
  exact h.symm

theorem opStable_ker (f : HCHom A B) : A.str.weight.OpStable (LinearMap.ker f.toLinearMap) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro v hv <;> rw [LinearMap.mem_ker] at hv ⊢
  · rw [f.map_H, hv, map_zero]
  · rw [f.map_X, hv, map_zero]
  · rw [f.map_Y, hv, map_zero]

/-- `range f` is homogeneous, dually.

@census none
-/
theorem isHomog_range (f : HCHom A B) :
    B.str.weight.IsHomog (LinearMap.range f.toLinearMap) := by
  rintro n v ⟨a, rfl⟩
  refine ⟨A.str.weight.proj n a, ?_⟩
  exact (WeightData.proj_comm_of_map A.str.weight B.str.weight f.toLinearMap
    (fun m w hw => f.map_comp_mem m w hw) n a).symm

theorem opStable_range (f : HCHom A B) :
    B.str.weight.OpStable (LinearMap.range f.toLinearMap) := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro v ⟨a, rfl⟩
  · exact ⟨A.str.weight.H a, f.map_H a⟩
  · exact ⟨A.str.weight.X a, f.map_X a⟩
  · exact ⟨A.str.weight.Y a, f.map_Y a⟩

/-- **Left cancellation.**  A linear map that becomes a morphism after composing with an injective
morphism is itself a morphism.  Used to descend the lift of a normal mono.

@census none
-/
def ofInjectiveComp (f : HCHom A B) (hinj : Function.Injective f.toLinearMap) (k : HCHom T B)
    (l : T.carrier →ₗ[ℂ] A.carrier) (hl : ∀ t, f.toLinearMap (l t) = k.toLinearMap t) :
    HCHom T A where
  toLinearMap := l
  map_H v := hinj (by rw [hl, k.map_H, f.map_H, hl])
  map_X v := hinj (by rw [hl, k.map_X, f.map_X, hl])
  map_Y v := hinj (by rw [hl, k.map_Y, f.map_Y, hl])
  map_rep g v := hinj (by rw [hl, k.map_rep, f.map_rep, hl])

/-- **Right cancellation.**  A linear map that becomes a morphism after precomposing with a
surjective morphism is itself a morphism.  Used to descend the co-lift of a normal epi.

@census none
-/
def ofCompSurjective (f : HCHom A B) (hsurj : Function.Surjective f.toLinearMap) (k : HCHom A T)
    (l : B.carrier →ₗ[ℂ] T.carrier) (hl : ∀ a, l (f.toLinearMap a) = k.toLinearMap a) :
    HCHom B T where
  toLinearMap := l
  map_H v := by
    obtain ⟨a, rfl⟩ := hsurj v
    rw [← f.map_H, hl, hl, k.map_H]
  map_X v := by
    obtain ⟨a, rfl⟩ := hsurj v
    rw [← f.map_X, hl, hl, k.map_X]
  map_Y v := by
    obtain ⟨a, rfl⟩ := hsurj v
    rw [← f.map_Y, hl, hl, k.map_Y]
  map_rep g v := by
    obtain ⟨a, rfl⟩ := hsurj v
    rw [← f.map_rep, hl, hl, k.map_rep]

/-! ### `HCHom` is an abelian group, and `HC(𝔤,K)` is preadditive -/

instance : Zero (HCHom A B) :=
  ⟨⟨0, fun _ => by simp, fun _ => by simp, fun _ => by simp, fun _ _ => by simp⟩⟩

@[simp] theorem zero_toLinearMap : (0 : HCHom A B).toLinearMap = 0 := rfl

instance : Add (HCHom A B) :=
  ⟨fun f g => ⟨f.toLinearMap + g.toLinearMap,
    fun v => by simp [f.map_H, g.map_H],
    fun v => by simp [f.map_X, g.map_X],
    fun v => by simp [f.map_Y, g.map_Y],
    fun h v => by simp [f.map_rep, g.map_rep]⟩⟩

@[simp] theorem add_toLinearMap (f g : HCHom A B) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap := rfl

instance : Neg (HCHom A B) :=
  ⟨fun f => ⟨-f.toLinearMap,
    fun v => by simp [f.map_H],
    fun v => by simp [f.map_X],
    fun v => by simp [f.map_Y],
    fun h v => by simp [f.map_rep]⟩⟩

@[simp] theorem neg_toLinearMap (f : HCHom A B) : (-f).toLinearMap = -f.toLinearMap := rfl

instance : Sub (HCHom A B) :=
  ⟨fun f g => ⟨f.toLinearMap - g.toLinearMap,
    fun v => by simp [f.map_H, g.map_H],
    fun v => by simp [f.map_X, g.map_X],
    fun v => by simp [f.map_Y, g.map_Y],
    fun h v => by simp [f.map_rep, g.map_rep]⟩⟩

@[simp] theorem sub_toLinearMap (f g : HCHom A B) :
    (f - g).toLinearMap = f.toLinearMap - g.toLinearMap := rfl

instance : SMul ℕ (HCHom A B) :=
  ⟨fun n f => ⟨n • f.toLinearMap,
    fun v => by simp [f.map_H],
    fun v => by simp [f.map_X],
    fun v => by simp [f.map_Y],
    fun h v => by simp [f.map_rep]⟩⟩

@[simp] theorem nsmul_toLinearMap (n : ℕ) (f : HCHom A B) :
    (n • f).toLinearMap = n • f.toLinearMap := rfl

instance : SMul ℤ (HCHom A B) :=
  ⟨fun n f => ⟨n • f.toLinearMap,
    fun v => by simp [f.map_H],
    fun v => by simp [f.map_X],
    fun v => by simp [f.map_Y],
    fun h v => by simp [f.map_rep]⟩⟩

@[simp] theorem zsmul_toLinearMap (n : ℤ) (f : HCHom A B) :
    (n • f).toLinearMap = n • f.toLinearMap := rfl

instance : AddCommGroup (HCHom A B) :=
  Function.Injective.addCommGroup HCHom.toLinearMap toLinearMap_injective rfl
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

end HCHom

/-- `HC(𝔤,K)` is **preadditive**: composition is bilinear for the pointwise addition of morphisms.

@census none
-/
instance : CategoryTheory.Preadditive HCObj.{u} where
  homGroup A B := (inferInstance : AddCommGroup (HCHom A B))
  add_comp _ _ _ f f' g := by
    apply HCHom.hom_ext
    exact LinearMap.comp_add _ _ _
  comp_add _ _ _ f g g' := by
    apply HCHom.hom_ext
    exact LinearMap.add_comp _ _ _

/-! ### The zero object -/

theorem isZero_zero : CategoryTheory.Limits.IsZero (HCObj.zero.{u}) := by
  haveI : Subsingleton (HCObj.zero.{u}).carrier := inferInstanceAs (Subsingleton PUnit.{u + 1})
  constructor
  · intro Y
    refine ⟨⟨⟨0⟩, fun f => ?_⟩⟩
    apply HCHom.hom_ext
    refine LinearMap.ext fun v => ?_
    rw [Subsingleton.elim v 0, map_zero, map_zero]
  · intro Y
    refine ⟨⟨⟨0⟩, fun f => ?_⟩⟩
    apply HCHom.hom_ext
    exact LinearMap.ext fun v => Subsingleton.elim _ _

instance : CategoryTheory.Limits.HasZeroObject HCObj.{u} := ⟨⟨_, isZero_zero⟩⟩


/-! ### Monos are injective, epis are surjective -/

namespace HCHom

variable {A B : HCObj.{u}}

theorem mono_of_injective {f : A ⟶ B} (h : Function.Injective f.toLinearMap) :
    CategoryTheory.Mono f :=
  ⟨fun {T} g₁ g₂ heq => by
    apply HCHom.hom_ext
    refine LinearMap.ext fun v => h ?_
    exact congrArg (fun t : T ⟶ B => t.toLinearMap v) heq⟩

theorem epi_of_surjective {f : A ⟶ B} (h : Function.Surjective f.toLinearMap) :
    CategoryTheory.Epi f :=
  ⟨fun {T} g₁ g₂ heq => by
    apply HCHom.hom_ext
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, rfl⟩ := h v
    exact congrArg (fun t : A ⟶ T => t.toLinearMap a) heq⟩

end HCHom

/-! ### Kernels -/

/-- The kernel object of a morphism: the sub-object on `ker f`, whose finite generation is
`HC/Noetherian.lean`'s theorem.

@census none
-/
noncomputable def kernelObj {A B : HCObj.{u}} (f : A ⟶ B) : HCObj.{u} :=
  A.sub f.opStable_ker f.isHomog_ker

/-- The inclusion of the kernel object.

@census none
-/
noncomputable def kernelι {A B : HCObj.{u}} (f : A ⟶ B) : kernelObj f ⟶ A where
  toLinearMap := (LinearMap.ker f.toLinearMap).subtype
  map_H _ := rfl
  map_X _ := rfl
  map_Y _ := rfl
  map_rep _ _ := rfl

theorem kernelι_comp {A B : HCObj.{u}} (f : A ⟶ B) : kernelι f ≫ f = 0 := by
  apply HCHom.hom_ext
  refine LinearMap.ext fun v => ?_
  exact LinearMap.mem_ker.mp v.2

/-- The kernel fork is a limit: a morphism killed by `f` factors, uniquely, through `ker f`.

@census none
-/
noncomputable def kernelIsLimit {A B : HCObj.{u}} (f : A ⟶ B) :
    Limits.IsLimit (Limits.KernelFork.ofι (kernelι f) (kernelι_comp f)) := by
  haveI : CategoryTheory.Mono (kernelι f) := HCHom.mono_of_injective Subtype.coe_injective
  refine Limits.KernelFork.IsLimit.ofι' (kernelι f) (kernelι_comp f) (fun {T} k hk => ?_)
  have hmem : ∀ t : T.carrier, k.toLinearMap t ∈ LinearMap.ker f.toLinearMap := by
    intro t
    have h := congrArg (fun z : T ⟶ B => z.toLinearMap t) hk
    exact LinearMap.mem_ker.mpr h
  refine ⟨{ toLinearMap := LinearMap.codRestrict _ k.toLinearMap hmem
            map_H := fun v => Subtype.ext (k.map_H v)
            map_X := fun v => Subtype.ext (k.map_X v)
            map_Y := fun v => Subtype.ext (k.map_Y v)
            map_rep := fun g v => Subtype.ext (k.map_rep g v) }, ?_⟩
  apply HCHom.hom_ext
  rfl

noncomputable instance : Limits.HasKernels HCObj.{u} :=
  ⟨fun f => Limits.HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

/-! ### Cokernels -/

/-- The cokernel object of a morphism: the quotient of the target by `range f`.

@census none
-/
noncomputable def cokernelObj {A B : HCObj.{u}} (f : A ⟶ B) : HCObj.{u} :=
  B.quot f.opStable_range f.isHomog_range

/-- The projection onto the cokernel object.

@census none
-/
noncomputable def cokernelπ {A B : HCObj.{u}} (f : A ⟶ B) : B ⟶ cokernelObj f where
  toLinearMap := (LinearMap.range f.toLinearMap).mkQ
  map_H _ := rfl
  map_X _ := rfl
  map_Y _ := rfl
  map_rep _ _ := rfl

theorem comp_cokernelπ {A B : HCObj.{u}} (f : A ⟶ B) : f ≫ cokernelπ f = 0 := by
  apply HCHom.hom_ext
  refine LinearMap.ext fun v => ?_
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩

/-- The cokernel cofork is a colimit.

@census none
-/
noncomputable def cokernelIsColimit {A B : HCObj.{u}} (f : A ⟶ B) :
    Limits.IsColimit (Limits.CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)) := by
  haveI : CategoryTheory.Epi (cokernelπ f) :=
    HCHom.epi_of_surjective (Submodule.mkQ_surjective _)
  refine Limits.CokernelCofork.IsColimit.ofπ' (cokernelπ f) (comp_cokernelπ f)
    (fun {T} k hk => ?_)
  have hle : LinearMap.range f.toLinearMap ≤ LinearMap.ker k.toLinearMap := by
    rintro _ ⟨a, rfl⟩
    exact LinearMap.mem_ker.mpr (congrArg (fun z : A ⟶ T => z.toLinearMap a) hk)
  refine ⟨{ toLinearMap := (LinearMap.range f.toLinearMap).liftQ k.toLinearMap hle
            map_H := fun x => by
              obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
              exact k.map_H b
            map_X := fun x => by
              obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
              exact k.map_X b
            map_Y := fun x => by
              obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
              exact k.map_Y b
            map_rep := fun g x => by
              obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
              exact k.map_rep g b }, ?_⟩
  apply HCHom.hom_ext
  exact Submodule.liftQ_mkQ _ _ _

noncomputable instance : Limits.HasCokernels HCObj.{u} :=
  ⟨fun f => Limits.HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

/-! ### Binary products, the terminal object, and finite products -/

/-- First projection of the product object.

@census none
-/
noncomputable def prodFst (A B : HCObj.{u}) : A.prod B ⟶ A where
  toLinearMap := LinearMap.fst ℂ A.carrier B.carrier
  map_H _ := rfl
  map_X _ := rfl
  map_Y _ := rfl
  map_rep _ _ := rfl

/-- Second projection of the product object.

@census none
-/
noncomputable def prodSnd (A B : HCObj.{u}) : A.prod B ⟶ B where
  toLinearMap := LinearMap.snd ℂ A.carrier B.carrier
  map_H _ := rfl
  map_X _ := rfl
  map_Y _ := rfl
  map_rep _ _ := rfl

/-- The universal map into the product object.

@census none
-/
noncomputable def prodLift {T A B : HCObj.{u}} (f : T ⟶ A) (g : T ⟶ B) : T ⟶ A.prod B where
  toLinearMap := f.toLinearMap.prod g.toLinearMap
  map_H v := Prod.ext (f.map_H v) (g.map_H v)
  map_X v := Prod.ext (f.map_X v) (g.map_X v)
  map_Y v := Prod.ext (f.map_Y v) (g.map_Y v)
  map_rep h v := Prod.ext (f.map_rep h v) (g.map_rep h v)

/-- The product object is the binary product.

@census none
-/
noncomputable def prodIsLimit (A B : HCObj.{u}) :
    Limits.IsLimit (Limits.BinaryFan.mk (prodFst A B) (prodSnd A B)) :=
  Limits.BinaryFan.IsLimit.mk _ (fun f g => prodLift f g) (fun _ _ => by apply HCHom.hom_ext; rfl)
    (fun _ _ => by apply HCHom.hom_ext; rfl)
    (fun f g m h1 h2 => by
      apply HCHom.hom_ext
      refine LinearMap.ext fun v => Prod.ext ?_ ?_
      · exact congrArg (fun t : _ ⟶ A => t.toLinearMap v) h1
      · exact congrArg (fun t : _ ⟶ B => t.toLinearMap v) h2)

noncomputable instance (A B : HCObj.{u}) : Limits.HasLimit (Limits.pair A B) :=
  Limits.HasLimit.mk ⟨_, prodIsLimit A B⟩

noncomputable instance : Limits.HasBinaryProducts HCObj.{u} :=
  Limits.hasBinaryProducts_of_hasLimit_pair _

noncomputable instance : Limits.HasTerminal HCObj.{u} := isZero_zero.isTerminal.hasTerminal

noncomputable instance : Limits.HasFiniteProducts HCObj.{u} :=
  hasFiniteProducts_of_has_binary_and_terminal

/-! ### Every mono is a kernel, every epi is a cokernel -/

theorem injective_of_mono {A B : HCObj.{u}} (f : A ⟶ B) [CategoryTheory.Mono f] :
    Function.Injective f.toLinearMap := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  have hzz : kernelι f ≫ f = (0 : kernelObj f ⟶ A) ≫ f := by
    rw [kernelι_comp, Limits.zero_comp]
  have h0 : kernelι f = 0 := (CategoryTheory.cancel_mono f).mp hzz
  exact congrArg (fun t : kernelObj f ⟶ A => t.toLinearMap ⟨v, hv⟩) h0

theorem surjective_of_epi {A B : HCObj.{u}} (f : A ⟶ B) [CategoryTheory.Epi f] :
    Function.Surjective f.toLinearMap := by
  have hzz : f ≫ cokernelπ f = f ≫ (0 : B ⟶ cokernelObj f) := by
    rw [comp_cokernelπ, Limits.comp_zero]
  have h0 : cokernelπ f = 0 := (CategoryTheory.cancel_epi f).mp hzz
  intro b
  have hb : (Submodule.Quotient.mk b : B.carrier ⧸ LinearMap.range f.toLinearMap) = 0 :=
    congrArg (fun t : B ⟶ cokernelObj f => t.toLinearMap b) h0
  exact (Submodule.Quotient.mk_eq_zero _).mp hb

/-- A mono is the kernel of its cokernel.

@census none
-/
@[implicit_reducible]
noncomputable def normalMonoOfMono {A B : HCObj.{u}} (f : A ⟶ B) [CategoryTheory.Mono f] :
    CategoryTheory.NormalMono f where
  Z := cokernelObj f
  g := cokernelπ f
  w := comp_cokernelπ f
  isLimit := by
    refine Limits.KernelFork.IsLimit.ofι' f (comp_cokernelπ f) (fun {T} k hk => ?_)
    have hinj := injective_of_mono f
    have hmem : ∀ t : T.carrier, k.toLinearMap t ∈ LinearMap.range f.toLinearMap := by
      intro t
      have h := congrArg (fun z : T ⟶ cokernelObj f => z.toLinearMap t) hk
      exact (Submodule.Quotient.mk_eq_zero _).mp h
    set e := LinearEquiv.ofInjective f.toLinearMap hinj with he
    set l0 : T.carrier →ₗ[ℂ] A.carrier :=
      e.symm.toLinearMap ∘ₗ
        LinearMap.codRestrict (LinearMap.range f.toLinearMap) k.toLinearMap hmem with hl0
    have hl : ∀ t, f.toLinearMap (l0 t) = k.toLinearMap t := by
      intro t
      have h1 : e (l0 t) = (⟨k.toLinearMap t, hmem t⟩ : LinearMap.range f.toLinearMap) := by
        rw [hl0]
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply]
        rfl
      exact congrArg Subtype.val h1
    exact ⟨HCHom.ofInjectiveComp f hinj k l0 hl, by apply HCHom.hom_ext; exact LinearMap.ext hl⟩

/-- An epi is the cokernel of its kernel.

@census none
-/
@[implicit_reducible]
noncomputable def normalEpiOfEpi {A B : HCObj.{u}} (f : A ⟶ B) [CategoryTheory.Epi f] :
    CategoryTheory.NormalEpi f where
  W := kernelObj f
  g := kernelι f
  w := kernelι_comp f
  isColimit := by
    refine Limits.CokernelCofork.IsColimit.ofπ' f (kernelι_comp f) (fun {T} k hk => ?_)
    have hsurj := surjective_of_epi f
    have hle : LinearMap.ker f.toLinearMap ≤ LinearMap.ker k.toLinearMap := by
      intro v hv
      exact LinearMap.mem_ker.mpr
        (congrArg (fun z : kernelObj f ⟶ T => z.toLinearMap ⟨v, hv⟩) hk)
    set e := LinearMap.quotKerEquivOfSurjective f.toLinearMap hsurj with he
    set l0 : B.carrier →ₗ[ℂ] T.carrier :=
      ((LinearMap.ker f.toLinearMap).liftQ k.toLinearMap hle) ∘ₗ e.symm.toLinearMap with hl0
    have hl : ∀ a, l0 (f.toLinearMap a) = k.toLinearMap a := by
      intro a
      have h1 : e.symm (f.toLinearMap a) = (Submodule.Quotient.mk a : _ ⧸ _) := by
        rw [LinearEquiv.symm_apply_eq, he]
        exact (LinearMap.quotKerEquivOfSurjective_apply_mk f.toLinearMap hsurj a).symm
      rw [hl0]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h1]
      exact Submodule.liftQ_apply _ _ _
    exact ⟨HCHom.ofCompSurjective f hsurj k l0 hl, by apply HCHom.hom_ext; exact LinearMap.ext hl⟩

instance : CategoryTheory.IsNormalMonoCategory HCObj.{u} where
  normalMonoOfMono f := ⟨normalMonoOfMono f⟩

instance : CategoryTheory.IsNormalEpiCategory HCObj.{u} where
  normalEpiOfEpi f := ⟨normalEpiOfEpi f⟩

/-- The `Abelian` structure on `HC(𝔤,K)`, assembled from the six pieces above.

@census none
-/
@[implicit_reducible]
noncomputable def harishChandraCatAbelian : Abelian HCObj.{u} where


/-- Clause `RQ2-3.11-C4`: `HC(𝔤,K)` is an **abelian** category.

Stated as `Nonempty (Abelian …)` because `CategoryTheory.Abelian` is a class carrying data
(kernels, cokernels, the coimage-image comparison) and a `def` may not have a `sorry` body at G2;
`Nonempty` of it is the `Prop` that says the structure exists, which is exactly the source's claim.

@census    none (auxiliary; discharges clause `RQ2-3.11-C4` of `RQ2-3.11`)
@source    def:hcmodule
@clauses   RQ2-3.11-C4
@imports   none
@divergence none
-/
theorem harishChandraCat_abelian : Nonempty (Abelian HCObj.{u}) :=
  ⟨harishChandraCatAbelian⟩

/-! ## `RQ2-3.03` — the category `HC_λ(𝔤,K)_E` -/

/-- **The category `HC_λ(𝔤,K)_E`** (`§3.3`, census `RQ2-3.03`).

The **full** subcategory (clause `C1`) of Harish-Chandra modules with generalized infinitesimal
character `λ = ℓ²` (clause `C2`, `HasGeneralizedInfinitesimalCharacter`, `HC/Casimir.lean`) on which
`-1₂ ∈ SL₂(ℝ)` acts by `(-1)^{ℓ-1}` (clause `C3`, `centralCharacter`).  Fullness is mathlib's
`ObjectProperty.FullSubcategory`, which is a full subcategory by construction — nothing weaker is
expressible with it.

The classical complex category, kept on the v2 line (A-28). On the v2 line the claimant of
`def:HClambdaE` (`RQ2-3.03`) is the uniform `HC.HC` (`HC/Category.lean`); for `E = ℂ` the two
are compared by `rmk:HClambdaC` (`RQ2-3.15`, stage T4, WP-11c).

@census    none (the classical `HC_λ(𝔤,K)` over `ℂ`; v1 claimant of `RQ-3.03`, `CROSSWALK-v1-v2.tsv`)
-/
def Category (ℓ : ℕ) : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun A : HCObj.{u} =>
      HasGeneralizedInfinitesimalCharacter A.str.weight ℓ ∧ A.str.centralCharacter ℓ)

instance (ℓ : ℕ) : CategoryTheory.Category.{u, u + 1} (HC.Category.{u} ℓ) :=
  ObjectProperty.FullSubcategory.category _

/-! ## G5 — inhabitants of `HarishChandraModule`, `HCObj` and `HCHom`

`WORKFLOW.md` §4/G5 asks for a concrete inhabitant in the same commit, non-degenerate where
degeneracy is a live risk.  For `HarishChandraModule` there are **two** live risks: the **zero**
module (if the only object were `0`, every statement of `§3.3`–`§3.4` about `HC_λ(𝔤,K)` would be
vacuous), and — after `R-S7-6`, and equally after the author's ruling of 2026-09-10 that
supersedes it — **concentration in degree `0`** (a module with `M_n = 0` for all `n ≠ 0` satisfies
`differential` for *any* sign of `χ_n`, so it cannot tell whether the fixed convention is
consistent with the differential condition).  Two witnesses answer them:
`trivialHC`, the one-dimensional module `ℂ` in degree `0` (non-zero, an object of `HC_λ` at
`ℓ = 1`), and `stdHC`, the standard representation `F_2 = ℂ²` with `M_1 = ℂ×0`, `M_{-1} = 0×ℂ`,
`X ≠ 0 ≠ Y`, `rep` the exponential of the `H`-action — a genuine `(𝔤,K)`-module under the fixed
convention, an object of `HC_λ` at `ℓ = 2`.
-/

section Witness

/-- **G5 inhabitant of `HarishChandraModule`, one**: the trivial one-dimensional module `ℂ`.

It is non-degenerate in the sense that it is **not** the zero module (`trivialHCObj_nontrivial`),
and it is a genuine object of `HC_λ(𝔤,K)` for `ℓ = 1`: on it `C = H² - 2H + 4XY + 1 = 1 = 1²`.
It is concentrated in degree `0`, so it does not exercise the sign convention; that is `stdHC`'s
job.

@census none
-/
noncomputable def trivialHC : HarishChandraModule ℂ where
  weight := trivialWeightData ℂ ℂ
  rep := 1
  isotypic n v := by
    constructor
    · intro hv g
      by_cases h : n = 0
      · subst h
        show v = _ • v
        simp
      · have hv' : v ∈ topAtZero ℂ ℂ n := hv
        rw [topAtZero_ne_zero h, Submodule.mem_bot] at hv'
        subst hv'
        show (0 : ℂ) = _ • (0 : ℂ)
        simp
    · intro hv
      by_cases h : n = 0
      · subst h; exact mem_topAtZero_zero v
      · obtain ⟨g, hg⟩ := exists_chiChar_ne_one h
        have hvg : v = chiChar n g • v := hv g
        show v ∈ topAtZero ℂ ℂ n
        rw [topAtZero_ne_zero h, Submodule.mem_bot]
        have : (1 - chiChar n g) * v = 0 := by
          rw [sub_mul, one_mul]
          simpa [smul_eq_mul] using sub_eq_zero.mpr hvg
        rcases mul_eq_zero.mp this with h1 | h2
        · exact absurd (by linear_combination -h1) hg
        · exact h2
  differential n v hv := (trivialWeightData ℂ ℂ).differential_of_chiChar n v hv
  fg := by
    refine ⟨{1}, le_antisymm le_top ?_⟩
    intro v _
    refine Submodule.mem_sInf.mpr fun N hN => ?_
    have h1 : (1 : ℂ) ∈ N := hN.1 (by simp)
    have : v = v • (1 : ℂ) := by simp
    rw [this]
    exact N.smul_mem v h1
  admissible n := inferInstance

/-- The `HC(𝔤,K)`-object carried by the trivial module — the G5 inhabitant of `HCObj`.

@census none
-/
noncomputable def trivialHCObj : HCObj.{0} := ⟨ℂ, trivialHC⟩

/-- Non-degeneracy of the `HC(𝔤,K)` witness: it is **not** the zero object, so the statements of
`§3.3`–`§3.4` about `HC_λ(𝔤,K)` are not vacuously true for want of an object.

@census none
-/
theorem trivialHCObj_nontrivial : Nontrivial trivialHCObj.carrier := inferInstanceAs (Nontrivial ℂ)

/-- **`HC_λ(𝔤,K)` is not empty, and not only zero**: the trivial module is an object of
`HC.Category 1` — it has generalized infinitesimal character `λ = 1 = 1²` (its Casimir is `1`) and
`-1₂` acts on it by `(-1)^{1-1} = 1`.  With `trivialHCObj_nontrivial` this is the non-vacuity
statement `RQ2-3.03` needs: the category the whole of `§5` is about has a non-zero object.

@census none
-/
theorem trivialHC_mem_category :
    HasGeneralizedInfinitesimalCharacter trivialHCObj.str.weight 1
      ∧ trivialHCObj.str.centralCharacter 1 := by
  constructor
  · exact trivialWeightData_gic
  · intro v
    show (1 : Representation ℂ (SO2_QStructure ℝ) ℂ) _ v = _
    simp

/-- `HC_λ(𝔤,K)` at `ℓ = 1` is inhabited (`WORKFLOW.md` §4/G5.2 for `RQ2-3.03`).

@census none
-/
theorem category_one_nonempty : Nonempty (HC.Category.{0} 1) :=
  ⟨⟨trivialHCObj, trivialHC_mem_category⟩⟩

/-- The G5 inhabitant of `HCHom`: the identity morphism of the trivial object.

@census none
-/
noncomputable def trivialHCHom : HCHom trivialHCObj trivialHCObj := 𝟙 trivialHCObj

/-! ### The standard representation `F_2 = ℂ²` — the witness that exercises the sign convention

`e₁ = (1,0)` has weight `+1`, `e₂ = (0,1)` weight `−1`; `H = diag(1,−1)`, `X e₂ = e₁`, `X e₁ = 0`,
`Y e₁ = e₂`, `Y e₂ = 0`; `k ∈ SO(2,ℝ)` acts by `χ_1(k)` on `e₁` and `χ_{−1}(k)` on `e₂` — the
exponential of the `H`-action, which is what the differential condition demands.  The Casimir is
`4 = 2²`, so this is an object of `HC_λ(𝔤,K)` at `ℓ = 2` (the paper's `F_ℓ` of `§6.1` at `ℓ = 2`).
-/

/-- `M_n` for `F_2`: `M_1 = ℂ × 0`, `M_{-1} = 0 × ℂ`, else `⊥`.

@census none
-/
def stdComp (n : ℤ) : Submodule ℂ (ℂ × ℂ) :=
  if n = 1 then Submodule.fst ℂ ℂ ℂ else if n = -1 then Submodule.snd ℂ ℂ ℂ else ⊥

theorem stdComp_one : stdComp 1 = Submodule.fst ℂ ℂ ℂ := by simp [stdComp]

theorem stdComp_neg_one : stdComp (-1) = Submodule.snd ℂ ℂ ℂ := by simp [stdComp]

theorem stdComp_of_ne {n : ℤ} (h1 : n ≠ 1) (h2 : n ≠ -1) : stdComp n = ⊥ := by
  simp [stdComp, h1, h2]

theorem mem_stdComp_one {v : ℂ × ℂ} : v ∈ stdComp 1 ↔ v.2 = 0 := by
  rw [stdComp_one]; simp [Submodule.fst]

theorem mem_stdComp_neg_one {v : ℂ × ℂ} : v ∈ stdComp (-1) ↔ v.1 = 0 := by
  rw [stdComp_neg_one]; simp [Submodule.snd]

theorem stdComp_le_snd_of_ne_one {n : ℤ} (h : n ≠ 1) : stdComp n ≤ Submodule.snd ℂ ℂ ℂ := by
  by_cases h2 : n = -1
  · subst h2; rw [stdComp_neg_one]
  · rw [stdComp_of_ne h h2]; exact bot_le

theorem stdComp_le_fst_of_ne_neg_one {n : ℤ} (h : n ≠ -1) : stdComp n ≤ Submodule.fst ℂ ℂ ℂ := by
  by_cases h1 : n = 1
  · subst h1; rw [stdComp_one]
  · rw [stdComp_of_ne h1 h]; exact bot_le

theorem stdComp_isInternal : DirectSum.IsInternal stdComp := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨fun i => ?_, ?_⟩
  · by_cases h1 : i = 1
    · subst h1
      have hle : (⨆ j, ⨆ (_ : j ≠ (1 : ℤ)), stdComp j) ≤ Submodule.snd ℂ ℂ ℂ :=
        iSup_le fun j => iSup_le fun hj => stdComp_le_snd_of_ne_one hj
      rw [stdComp_one]
      exact (disjoint_iff.mpr (Submodule.fst_inf_snd ℂ ℂ ℂ)).mono_right hle
    · by_cases h2 : i = -1
      · subst h2
        have hle : (⨆ j, ⨆ (_ : j ≠ (-1 : ℤ)), stdComp j) ≤ Submodule.fst ℂ ℂ ℂ :=
          iSup_le fun j => iSup_le fun hj => stdComp_le_fst_of_ne_neg_one hj
        rw [stdComp_neg_one]
        exact (disjoint_iff.mpr (by rw [inf_comm]; exact Submodule.fst_inf_snd ℂ ℂ ℂ)).mono_right hle
      · rw [stdComp_of_ne h1 h2]
        exact disjoint_bot_left
  · apply le_antisymm le_top
    rw [← Submodule.fst_sup_snd ℂ ℂ ℂ]
    exact sup_le (le_iSup_of_le 1 (by rw [stdComp_one]))
      (le_iSup_of_le (-1) (by rw [stdComp_neg_one]))

/-- `H = diag(1, −1)` on `F_2`.

@census none
-/
def stdH : Module.End ℂ (ℂ × ℂ) := LinearMap.prod (LinearMap.fst ℂ ℂ ℂ) (-LinearMap.snd ℂ ℂ ℂ)

/-- `X : (a, b) ↦ (b, 0)` on `F_2` (`X e₂ = e₁`).

@census none
-/
def stdX : Module.End ℂ (ℂ × ℂ) := LinearMap.prod (LinearMap.snd ℂ ℂ ℂ) 0

/-- `Y : (a, b) ↦ (0, a)` on `F_2` (`Y e₁ = e₂`).

@census none
-/
def stdY : Module.End ℂ (ℂ × ℂ) := LinearMap.prod 0 (LinearMap.fst ℂ ℂ ℂ)

@[simp] theorem stdH_apply (v : ℂ × ℂ) : stdH v = (v.1, -v.2) := rfl
@[simp] theorem stdX_apply (v : ℂ × ℂ) : stdX v = (v.2, 0) := rfl
@[simp] theorem stdY_apply (v : ℂ × ℂ) : stdY v = (0, v.1) := rfl

/-- The `WeightData` of `F_2`.

@census none
-/
def stdWeight : WeightData ℂ (ℂ × ℂ) where
  comp := stdComp
  isInternal := stdComp_isInternal
  H := stdH
  X := stdX
  Y := stdY
  H_apply := by
    intro n v hv
    by_cases h1 : n = 1
    · subst h1
      rw [mem_stdComp_one] at hv
      apply Prod.ext <;> simp [hv]
    · by_cases h2 : n = -1
      · subst h2
        rw [mem_stdComp_neg_one] at hv
        apply Prod.ext <;> simp [hv]
      · rw [stdComp_of_ne h1 h2, Submodule.mem_bot] at hv
        subst hv
        simp
  X_mem := by
    intro n v hv
    by_cases h1 : n = 1
    · subst h1
      rw [mem_stdComp_one] at hv
      have : stdX v = 0 := by simp [Prod.ext_iff, hv]
      rw [this]
      exact Submodule.zero_mem _
    · by_cases h2 : n = -1
      · subst h2
        show stdX v ∈ stdComp (-1 + 2)
        rw [show (-1 : ℤ) + 2 = 1 by norm_num, mem_stdComp_one]
        simp
      · rw [stdComp_of_ne h1 h2, Submodule.mem_bot] at hv
        subst hv
        rw [map_zero]
        exact Submodule.zero_mem _
  Y_mem := by
    intro n v hv
    by_cases h1 : n = 1
    · subst h1
      show stdY v ∈ stdComp (1 - 2)
      rw [show (1 : ℤ) - 2 = -1 by norm_num, mem_stdComp_neg_one]
      simp
    · by_cases h2 : n = -1
      · subst h2
        rw [mem_stdComp_neg_one] at hv
        have : stdY v = 0 := by simp [Prod.ext_iff, hv]
        rw [this]
        exact Submodule.zero_mem _
      · rw [stdComp_of_ne h1 h2, Submodule.mem_bot] at hv
        subst hv
        rw [map_zero]
        exact Submodule.zero_mem _
  lie_H_X := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · simp; ring
    · simp
  lie_H_Y := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · simp
    · simp; ring
  lie_X_Y := by
    apply LinearMap.ext
    intro v
    apply Prod.ext <;> simp

@[simp] theorem stdWeight_comp : stdWeight.comp = stdComp := rfl
@[simp] theorem stdWeight_H : stdWeight.H = stdH := rfl
@[simp] theorem stdWeight_X : stdWeight.X = stdX := rfl
@[simp] theorem stdWeight_Y : stdWeight.Y = stdY := rfl

/-- The Casimir of `F_2` is `4 = 2²`.

@census none
-/
theorem stdWeight_casimir : stdWeight.casimir = (4 : ℂ) • (1 : Module.End ℂ (ℂ × ℂ)) := by
  apply LinearMap.ext
  intro v
  apply Prod.ext <;> simp [WeightData.casimir, sq] <;> ring

/-- The `SO(2,ℝ)`-action on `F_2`: `k · (a, b) = (χ_1(k) a, χ_{−1}(k) b)`.

@census none
-/
noncomputable def stdRep : Representation ℂ (SO2_QStructure ℝ) (ℂ × ℂ) where
  toFun g := LinearMap.prod (chiChar 1 g • LinearMap.fst ℂ ℂ ℂ) (chiChar (-1) g • LinearMap.snd ℂ ℂ ℂ)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Prod.ext <;> simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Prod.ext <;> simp [chiChar_mul, mul_assoc]

@[simp] theorem stdRep_apply (g : SO2_QStructure ℝ) (v : ℂ × ℂ) :
    stdRep g v = (chiChar 1 g * v.1, chiChar (-1) g * v.2) := rfl

/-- **G5 inhabitant of `HarishChandraModule`, two — the standard representation `F_2 = ℂ²`**,
non-degenerate in every sense that matters here: `M_1 ≠ 0` (`stdHC_comp_one_ne_bot`) and
`M_{-1} ≠ 0` (`stdHC_comp_neg_one_ne_bot`),
`X ≠ 0 ≠ Y` (`stdHC_X_ne_zero`, `stdHC_Y_ne_zero`), and the `K`-action is the exponential of the
`H`-action, so the field `differential` is discharged with `M_{±1} ≠ 0` — the convention in force
(the author's ruling of 2026-09-10, superseding `R-S7-6`) is consistent with the differential
condition off degree `0`.  It is an object of
`HC_λ(𝔤,K)` at `ℓ = 2` (`stdHC_mem_category`, `category_two_nonempty`).

@census none
-/
noncomputable def stdHC : HarishChandraModule (ℂ × ℂ) where
  weight := stdWeight
  rep := stdRep
  isotypic n v := by
    constructor
    · intro hv g
      by_cases h1 : n = 1
      · subst h1
        rw [stdWeight_comp, mem_stdComp_one] at hv
        apply Prod.ext <;> simp [hv]
      · by_cases h2 : n = -1
        · subst h2
          rw [stdWeight_comp, mem_stdComp_neg_one] at hv
          apply Prod.ext <;> simp [hv]
        · rw [stdWeight_comp, stdComp_of_ne h1 h2, Submodule.mem_bot] at hv
          subst hv
          simp
    · intro h
      have hfst : n ≠ 1 → v.1 = 0 := by
        intro hn
        apply eq_zero_of_forall_chiChar_mul_eq (m := n - 1) (sub_ne_zero.mpr hn)
        intro g
        have h1 : chiChar 1 g * v.1 = chiChar n g * v.1 := congrArg Prod.fst (h g)
        calc chiChar (n - 1) g * v.1 = chiChar (-1) g * (chiChar n g * v.1) := by
              rw [← mul_assoc, ← chiChar_add, neg_add_eq_sub]
          _ = chiChar (-1) g * (chiChar 1 g * v.1) := by rw [h1]
          _ = v.1 := by rw [← mul_assoc, ← chiChar_add, neg_add_cancel, chiChar_zero, one_mul]
      have hsnd : n ≠ -1 → v.2 = 0 := by
        intro hn
        apply eq_zero_of_forall_chiChar_mul_eq (m := n + 1)
          (by intro h0; exact hn (by linear_combination h0))
        intro g
        have h2 : chiChar (-1) g * v.2 = chiChar n g * v.2 := congrArg Prod.snd (h g)
        calc chiChar (n + 1) g * v.2 = chiChar 1 g * (chiChar n g * v.2) := by
              rw [← mul_assoc, ← chiChar_add, add_comm]
          _ = chiChar 1 g * (chiChar (-1) g * v.2) := by rw [h2]
          _ = v.2 := by rw [← mul_assoc, ← chiChar_add, add_neg_cancel, chiChar_zero, one_mul]
      by_cases h1 : n = 1
      · subst h1
        rw [stdWeight_comp, mem_stdComp_one]
        exact hsnd (by norm_num)
      · by_cases h2 : n = -1
        · subst h2
          rw [stdWeight_comp, mem_stdComp_neg_one]
          exact hfst (by norm_num)
        · rw [stdWeight_comp, stdComp_of_ne h1 h2, Submodule.mem_bot]
          exact Prod.ext (hfst h1) (hsnd h2)
  differential n v hv := stdWeight.differential_of_chiChar n v hv
  fg := by
    refine ⟨{((1 : ℂ), (0 : ℂ))}, le_antisymm le_top ?_⟩
    intro v _
    refine Submodule.mem_sInf.mpr fun N hN => ?_
    have h1 : ((1 : ℂ), (0 : ℂ)) ∈ N := hN.1 (by simp)
    have h2 : ((0 : ℂ), (1 : ℂ)) ∈ N := by
      have := hN.2.1 stdWeight.Y (by simp) _ h1
      simpa using this
    have : v = v.1 • ((1 : ℂ), (0 : ℂ)) + v.2 • ((0 : ℂ), (1 : ℂ)) := by
      apply Prod.ext <;> simp
    rw [this]
    exact N.add_mem (N.smul_mem _ h1) (N.smul_mem _ h2)
  admissible n := inferInstance

/-- The `HC(𝔤,K)`-object carried by `F_2`.

@census none
-/
noncomputable def stdHCObj : HCObj.{0} := ⟨ℂ × ℂ, stdHC⟩

/-- Non-degeneracy of `stdHC`, one: `M_1 ≠ 0` — a non-zero isotypic component in a degree `n ≠ 0`,
where the sign of `χ_n` matters.

@census none
-/
theorem stdHC_comp_one_ne_bot : stdHC.weight.comp 1 ≠ ⊥ := by
  intro h
  have h1 : ((1 : ℂ), (0 : ℂ)) ∈ stdHC.weight.comp 1 := mem_stdComp_one.mpr rfl
  rw [h, Submodule.mem_bot] at h1
  exact one_ne_zero (congrArg Prod.fst h1)

/-- Non-degeneracy of `stdHC`, one and a half: `M_{-1} ≠ 0`.  The companion of
`stdHC_comp_one_ne_bot`, so that the claim "`M_{±1} ≠ 0`" made in `stdHC`'s docstring and in
`RQ2-3.11`'s G6 cell is proved in full and not only in half (verifier finding `V-S7-D1-2`,
2026-09-02).

@census none
-/
theorem stdHC_comp_neg_one_ne_bot : stdHC.weight.comp (-1) ≠ ⊥ := by
  intro h
  have h1 : ((0 : ℂ), (1 : ℂ)) ∈ stdHC.weight.comp (-1) := mem_stdComp_neg_one.mpr rfl
  rw [h, Submodule.mem_bot] at h1
  exact one_ne_zero (congrArg Prod.snd h1)

/-- Non-degeneracy of `stdHC`, two: `X ≠ 0`.

@census none
-/
theorem stdHC_X_ne_zero : stdHC.weight.X ≠ 0 := by
  intro h
  have : stdX ((0 : ℂ), (1 : ℂ)) = 0 := by
    show stdHC.weight.X _ = 0
    rw [h]; rfl
  have := congrArg Prod.fst this
  simp at this

/-- Non-degeneracy of `stdHC`, three: `Y ≠ 0`.

@census none
-/
theorem stdHC_Y_ne_zero : stdHC.weight.Y ≠ 0 := by
  intro h
  have : stdY ((1 : ℂ), (0 : ℂ)) = 0 := by
    show stdHC.weight.Y _ = 0
    rw [h]; rfl
  have := congrArg Prod.snd this
  simp at this

/-- `F_2` is an object of `HC_λ(𝔤,K)` at `ℓ = 2`: its Casimir is `4 = 2²`, and `-1₂` acts on it by
`(-1)^{2-1} = -1` (`χ_{±1}(-1₂) = -1`).

@census none
-/
theorem stdWeight_gic : HasGeneralizedInfinitesimalCharacter stdWeight 2 := by
  refine ⟨1, ?_⟩
  have h4 : (algebraMap ℚ ℂ (((2 : ℕ) : ℚ) ^ 2)) = (4 : ℂ) := by norm_num
  rw [pow_one, stdWeight_casimir, h4, sub_self]

theorem stdHC_centralCharacter : stdHC.centralCharacter 2 := by
  intro v
  show stdRep (minusOnePt ℝ) v = _
  rw [stdRep_apply]
  apply Prod.ext <;> simp [chiChar, minusOnePt]

theorem stdHC_mem_category :
    HasGeneralizedInfinitesimalCharacter stdHCObj.str.weight 2
      ∧ stdHCObj.str.centralCharacter 2 :=
  ⟨stdWeight_gic, stdHC_centralCharacter⟩

/-- `HC_λ(𝔤,K)` at `ℓ = 2` has a non-zero object with `M_{±1} ≠ 0`.

@census none
-/
theorem category_two_nonempty : Nonempty (HC.Category.{0} 2) :=
  ⟨⟨stdHCObj, stdHC_mem_category⟩⟩

end Witness

end RationalQuivers.HC
