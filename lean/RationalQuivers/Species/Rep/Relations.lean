import RationalQuivers.Species.Rep.Basic

/-!
# Relations for a `K`-species (§2.5, census `RQ2-2.36`)

Formalizes Definition `def:speciesrelations`, the environment the paper's author added to §2.5 on
**2026-09-11** by the **option-(b)** ruling on `AN-33(iii)`
(`workflow/reports/AUTHOR-QUEUE.md`, the `AUTHOR RULING, 2026-09-11` block; the `latex/` edit
landed at `388f0f8`).  Census r14 books it as row `RQ2-2.36` with clauses `H1`, `C1`–`C5`;
coordinator ruling `R-ERR-1` of 2026-09-11 assigns the row to stage **S5**.

Until that ruling the tree had **no** intrinsic notion of a relation on species representations:
`RQ-5.06`'s species-side target was the *transported* `RepNilRelSpeciesGelfand`
(`Gelfand/Corollaries.lean`), which is option (a)'s shape and which the author declined.  This
module is the option-(b) obligation's first half — the **general** definition.  It is new
mathematics in S5, not a re-statement of anything already here.

## Main definitions / results

* `RationalQuivers.Species.Bimod` — an `(A,B)`-bimodule with every instance
  `Species/Rep/Tensor.lean`'s standing assumptions need, bundled so that the path bimodule can be
  built by recursion on the length of the path.
* `RationalQuivers.Species.pathBimod` — clause `RQ2-2.36-C1`: the **path bimodule**
  `{}_{i_0}M_p = {}_{i_0}M_{i_1} ⊗_{L_{i_1}} ⋯ ⊗_{L_{i_{n-1}}} {}_{i_{n-1}}M_{i_n}`, as an
  `(L_{i_0}, L_{i_n})`-bimodule.
* `RationalQuivers.Species.pathHom` — clause `RQ2-2.36-C2`: the iterated, `L_{i_n}`-linear
  composite `f_p : W_{i_0} ⊗_{L_{i_0}} {}_{i_0}M_p → W_{i_n}`.
* `RationalQuivers.Species.SubBimod`, `RationalQuivers.Species.Relation` — clause `RQ2-2.36-C3`: a
  relation is a family `R = (R_p)_p` of **sub-bimodules** `R_p ⊆ {}_{i_0}M_p`.
* `RationalQuivers.Species.Satisfies` — clause `RQ2-2.36-C4`: `f_p(W_{i_0} ⊗_{L_{i_0}} R_p) = 0`.
* `RationalQuivers.Species.RepRel`, `RationalQuivers.Species.RepNilRel` — clause `RQ2-2.36-C5`:
  the full subcategories `Rep(S,R) ⊆ Rep(S)` and `Rep^nil(S,R) ⊆ Rep(S,R)`.

## Implementation notes

**The bundled `Bimod`.**  `{}_{i_0}M_p` is an *iterated* balanced tensor product, and every step
of the iteration needs the eight instances `Balanced`'s standing assumptions list — on the object
the previous step produced.  Lean cannot carry those through a bare type-valued recursion, so they
travel with the carrier in the structure `Bimod`.  The step itself introduces nothing new: the
inherited left action is `Balanced.moduleLeftOfY`, its tower `Balanced.towerLeftOfY` and its
bimodule axiom `Balanced.smulCommLeftOfY`, all three built for `Balanced.assoc` at finding
**S5-F10**, and the right-hand data is `Submodule.Quotient`'s own.

**`f_p` is `Balanced.assoc` run along the path.**  The recursion step rewrites
`W_{i_0} ⊗_{L_{i_0}} ({}_{i_0}M_{p'} ⊗_{L_{i_n}} {}_{i_n}M_{i_{n+1}})` as
`(W_{i_0} ⊗_{L_{i_0}} {}_{i_0}M_{p'}) ⊗_{L_{i_n}} {}_{i_n}M_{i_{n+1}}` — the heterobasic
associativity of `Species/Rep/Tensor.lean` — applies `f_{p'} ⊗ 1` and then `f_{i_n i_{n+1}}`.
That is the source's own `f_{i_{n-1}i_n} ∘ (f_{i_{n-2}i_{n-1}} ⊗ 1) ∘ ⋯ ∘ (f_{i_0i_1} ⊗ 1)`,
read from the left; `pathHom_mk` is the bridge to the pure-tensor form and says that on
`w ⊗ (m_0 ⊗ ⋯ ⊗ m_n)` it is exactly `Species.Rep.pathApply`, the chain composite `DEF-S5-02`
already uses for nilpotency.

**Path indexing.**  A path of length `n + 1 ≥ 1` is `(idx : ℕ → S.I, n : ℕ)`, the encoding
`Species.Rep.pathApply` and `Species.Rep.IsNilpotent` (`DEF-S5-02`, author-ratified 2026-08-30)
already use; `pathBimod S idx n` mentions only `idx 0, …, idx (n+1)`.  See `Relation`'s
`@divergence` for what this costs.
-/

universe u

namespace RationalQuivers

open scoped TensorProduct

namespace Species

variable {K : Type u} [Field K]

/-! ### The bundled bimodule -/

/-- An `(A,B)`-bimodule together with every instance `Species/Rep/Tensor.lean`'s standing
assumptions need, bundled so that `pathBimod` can be built by recursion.

@census none (project definition; the carrier of clause `RQ2-2.36-C1`)
-/
structure Bimod (K : Type u) [Field K] (A B : Type u) [Ring A] [Algebra K A] [Ring B]
    [Algebra K B] : Type (u + 1) where
  /-- the underlying `K`-vector space -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [moduleK : Module K carrier]
  /-- the left `A`-action -/
  [moduleLeft : Module A carrier]
  /-- the right `B`-action -/
  [moduleRight : Module Bᵐᵒᵖ carrier]
  [smulComm_K : SMulCommClass K Bᵐᵒᵖ carrier]
  /-- the bimodule axiom -/
  [smulComm_LR : SMulCommClass A Bᵐᵒᵖ carrier]
  [tower_left : IsScalarTower K A carrier]
  [tower_right : IsScalarTower K Bᵐᵒᵖ carrier]

attribute [instance] Bimod.addCommGroup Bimod.moduleK Bimod.moduleLeft Bimod.moduleRight
  Bimod.smulComm_K Bimod.smulComm_LR Bimod.tower_left Bimod.tower_right

/-- `SMulCommClass K Bᵐᵒᵖ M` for any `Bᵐᵒᵖ`-module whose ambient `K`-structure is the induced one:
the image of `K` is central in `B`, hence in `Bᵐᵒᵖ`.  @census none (helper) -/
theorem smulCommClass_K_of_tower (B : Type u) [Ring B] [Algebra K B] (M : Type u)
    [AddCommGroup M] [Module K M] [Module Bᵐᵒᵖ M] [IsScalarTower K Bᵐᵒᵖ M] :
    SMulCommClass K Bᵐᵒᵖ M where
  smul_comm c b m := by
    have h : ∀ x : M, c • x = (algebraMap K Bᵐᵒᵖ) c • x := by
      intro x
      have h1 : (c • (1 : Bᵐᵒᵖ)) • x = c • ((1 : Bᵐᵒᵖ) • x) := smul_assoc c 1 x
      rw [one_smul, Algebra.smul_def, mul_one] at h1
      exact h1.symm
    rw [h, h, ← mul_smul, ← mul_smul, Algebra.commutes]

variable (S : Species K)

/-! ### `RQ2-2.36-C1` — the path bimodule -/

/-- **Clause `RQ2-2.36-C1`** — the **path bimodule** of the path `p = (idx 0, …, idx (n+1))`:
`{}_{i_0}M_p := {}_{i_0}M_{i_1} ⊗_{L_{i_1}} ⋯ ⊗_{L_{i_n}} {}_{i_n}M_{i_{n+1}}`, an
`(L_{i_0}, L_{i_{n+1}})`-**bimodule**.

The paper's path has length `n ≥ 1`; here the length is `n + 1`, so that `n : ℕ` is unrestricted
(the same shift `Species.Rep.pathApply` makes).  The left `L_{i_0}`-action is inherited from the
leftmost factor at every step (`Balanced.moduleLeftOfY`) and the right `L_{i_{n+1}}`-action is the
rightmost factor's, which is what makes the object an `(L_{i_0}, L_{i_{n+1}})`-bimodule and not
merely a `K`-vector space.

@census    none (auxiliary; discharges clause `RQ2-2.36-C1` of `RQ2-2.36`)
@source    def:speciesrelations
@clauses   RQ2-2.36-C1
@imports   none
@divergence none
-/
noncomputable def pathBimod (idx : ℕ → S.I) :
    (n : ℕ) → Bimod K (S.L (idx 0)) (S.L (idx (n + 1)))
  | 0 => { carrier := S.M (idx 0) (idx 1)
           smulComm_K := Species.smulCommClass_K_M S (idx 0) (idx 1)
           tower_right := Species.isScalarTower_right_M S (idx 0) (idx 1) }
  | (n + 1) =>
      { carrier := Balanced K (S.L (idx (n + 1))) (S.L (idx (n + 2)))
          (S.M (idx (n + 1)) (idx (n + 2))) (pathBimod idx n).carrier
        moduleLeft := Balanced.moduleLeftOfY K (S.L (idx 0)) (S.L (idx (n + 1)))
          (S.L (idx (n + 2))) (pathBimod idx n).carrier (S.M (idx (n + 1)) (idx (n + 2)))
        smulComm_K := smulCommClass_K_of_tower _ _
        smulComm_LR := Balanced.smulCommLeftOfY K (S.L (idx 0)) (S.L (idx (n + 1)))
          (S.L (idx (n + 2))) (pathBimod idx n).carrier (S.M (idx (n + 1)) (idx (n + 2)))
        tower_left := Balanced.towerLeftOfY K (S.L (idx 0)) (S.L (idx (n + 1)))
          (S.L (idx (n + 2))) (pathBimod idx n).carrier (S.M (idx (n + 1)) (idx (n + 2))) }

/-- The path bimodule of a length-one path is the edge bimodule itself.
@census none (value guard for `RQ2-2.36-C1`) -/
theorem pathBimod_zero (idx : ℕ → S.I) : (pathBimod S idx 0).carrier = S.M (idx 0) (idx 1) := rfl

/-- The recursion step of `RQ2-2.36-C1`, as an equation of carriers.
@census none (value guard for `RQ2-2.36-C1`) -/
theorem pathBimod_succ (idx : ℕ → S.I) (n : ℕ) :
    (pathBimod S idx (n + 1)).carrier
      = Balanced K (S.L (idx (n + 1))) (S.L (idx (n + 2))) (S.M (idx (n + 1)) (idx (n + 2)))
          (pathBimod S idx n).carrier := rfl

/-! ### `RQ2-2.36-C2` — the iterated composite `f_p` -/

/-- `W_{i_0} ⊗_{L_{i_0}} {}_{i_0}M_p`, the source of `f_p`.  @census none (helper) -/
abbrev pathTensor (V : Rep S) (idx : ℕ → S.I) (n : ℕ) : Type u :=
  Balanced K (S.L (idx 0)) (S.L (idx (n + 1))) (pathBimod S idx n).carrier (V.W (idx 0))

/-- **Clause `RQ2-2.36-C2`** — the **iterated composite**
`f_p = f_{i_n i_{n+1}} ∘ (f_{i_{n-1} i_n} ⊗ 1) ∘ ⋯ ∘ (f_{i_0 i_1} ⊗ 1) :
W_{i_0} ⊗_{L_{i_0}} {}_{i_0}M_p → W_{i_{n+1}}`, and it is **`L_{i_{n+1}}`-linear** — which is
what the `→ₗ[(S.L (idx (n+1)))ᵐᵒᵖ]` in the type says, the right `L_{i_{n+1}}`-action being
mathlib's spelling of an `L_{i_{n+1}}`-vector-space map here (`Species/Rep/Basic.lean`).

The step is `Balanced.assoc` (the heterobasic associativity of `Species/Rep/Tensor.lean`,
finding **S5-F10**) followed by `f_{p'} ⊗ 1` and then by the last structure map.

@census    none (auxiliary; discharges clause `RQ2-2.36-C2` of `RQ2-2.36`)
@source    def:speciesrelations
@clauses   RQ2-2.36-C2
@imports   none
@divergence none
-/
noncomputable def pathHom (V : Rep S) (idx : ℕ → S.I) :
    (n : ℕ) → pathTensor S V idx n →ₗ[(S.L (idx (n + 1)))ᵐᵒᵖ] V.W (idx (n + 1))
  | 0 => V.f (idx 0) (idx 1)
  | (n + 1) =>
      (V.f (idx (n + 1)) (idx (n + 2))).comp
        ((Balanced.map (K := K) (A := S.L (idx (n + 1)))
            (Y := S.M (idx (n + 1)) (idx (n + 2)))
            (X := pathTensor S V idx n) (X' := V.W (idx (n + 1)))
            (fun c x => Balanced.smul_K (A := S.L (idx 0)) (B := S.L (idx (n + 1))) c x)
            (V.smul_K_W (idx (n + 1))) (pathHom V idx n) (S.L (idx (n + 2)))).comp
          (Balanced.assoc (K := K) (A := S.L (idx 0)) (B := S.L (idx (n + 1)))
            (C := S.L (idx (n + 2))) (Y := (pathBimod S idx n).carrier)
            (Z := S.M (idx (n + 1)) (idx (n + 2))) (X := V.W (idx 0))).symm.toLinearMap)

/-- `f_p` on a path of length one is the structure map itself.
@census none (value guard for `RQ2-2.36-C2`) -/
theorem pathHom_zero (V : Rep S) (idx : ℕ → S.I) :
    pathHom S V idx 0 = V.f (idx 0) (idx 1) := rfl

/-- The pure tensor `m_0 ⊗ ⋯ ⊗ m_n ∈ {}_{i_0}M_p`.  @census none (helper) -/
noncomputable def pathElt (idx : ℕ → S.I) (m : ∀ k, S.M (idx k) (idx (k + 1))) :
    (n : ℕ) → (pathBimod S idx n).carrier
  | 0 => m 0
  | (n + 1) => Balanced.mk (pathElt idx m n) (m (n + 1))

/-- **`f_p` is the chain composite.**  On a pure tensor `w ⊗ (m_0 ⊗ ⋯ ⊗ m_n)`, `pathHom` is
`Species.Rep.pathApply` — the composite of structure maps along the chain that `DEF-S5-02` uses
for nilpotency.  This is what says the iterated map of clause `RQ2-2.36-C2` is the source's, and it
is the bridge between this module and `Species.Rep.IsNilpotent`.

@census none (clause witness for `RQ2-2.36-C2`)
@clauses   RQ2-2.36-C2
-/
theorem pathHom_mk (V : Rep S) (idx : ℕ → S.I) (m : ∀ k, S.M (idx k) (idx (k + 1))) :
    ∀ (n : ℕ) (w : V.W (idx 0)),
      pathHom S V idx n (Balanced.mk w (pathElt S idx m n)) = V.pathApply idx m (n + 1) w
  | 0, w => rfl
  | (n + 1), w => by
      have ih := pathHom_mk V idx m n w
      show V.f (idx (n + 1)) (idx (n + 2))
          (Balanced.map _ _ (pathHom S V idx n) _
            (Balanced.mk (Balanced.mk w (pathElt S idx m n)) (m (n + 1)))) = _
      rw [Balanced.map_mk, ih]
      rfl

/-! ### `RQ2-2.36-C3` — relations -/

/-- A **sub-bimodule** of an `(A,B)`-bimodule: a left `A`-submodule that is also closed under the
right `B`-action.  (Closure under the ambient `K` is then automatic, `K` acting through `B`.)

@census none (project definition; the carrier of clause `RQ2-2.36-C3`)
-/
structure SubBimod {A B : Type u} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (P : Bimod K A B) : Type u where
  /-- the underlying left `A`-submodule -/
  toSubmodule : Submodule A P.carrier
  /-- closed under the right `B`-action -/
  smul_right_mem : ∀ (b : Bᵐᵒᵖ) {x : P.carrier}, x ∈ toSubmodule → b • x ∈ toSubmodule

/-- The zero sub-bimodule.  @census none (helper) -/
def SubBimod.bot {A B : Type u} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (P : Bimod K A B) : SubBimod P where
  toSubmodule := ⊥
  smul_right_mem b x hx := by
    rw [Submodule.mem_bot] at hx ⊢; rw [hx, smul_zero]

/-- The whole bimodule, as a sub-bimodule.  @census none (helper) -/
def SubBimod.top {A B : Type u} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (P : Bimod K A B) : SubBimod P where
  toSubmodule := ⊤
  smul_right_mem _ _ _ := Submodule.mem_top

/-- Everything lies in the maximal sub-bimodule.  @census none (helper) -/
theorem SubBimod.mem_top {A B : Type u} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (P : Bimod K A B) (x : P.carrier) : x ∈ (SubBimod.top P).toSubmodule := Submodule.mem_top

/-- **Definition** (`def:speciesrelations`, §2.5, census `RQ2-2.36`).

Let `S = (L_i, {}_iM_j)_{i,j ∈ I}` be a `K`-species (clause `RQ2-2.36-H1`, the argument `S`).  A
**relation** for `S` is a family `R = (R_p)_p`, indexed by the paths `p` in `I` of length `≥ 1`,
of `L_{i_0},L_{i_n}`-**sub-bimodules** `R_p ⊆ {}_{i_0}M_p` (clause `RQ2-2.36-C3`), where
`{}_{i_0}M_p` is the path bimodule `pathBimod` (clause `RQ2-2.36-C1`).

Satisfaction (clause `RQ2-2.36-C4`) is `Satisfies`, and the two full subcategories of clause
`RQ2-2.36-C5` are `RepRel` and `RepNilRel`; the iterated map `f_p` of clause `RQ2-2.36-C2` is
`pathHom`.

@census    RQ2-2.36
@source    def:speciesrelations
@clauses   RQ2-2.36-H1, RQ2-2.36-C3
@imports   none
@divergence JUSTIFIED_REFORMULATION (the path-indexing convention, disclosed).  The source indexes
the family by the *paths* `p = (i_0, …, i_n)` of `I`; here the index is a pair `(idx : ℕ → S.I,
n : ℕ)` standing for the path `(idx 0, …, idx (n+1))` — the encoding `Species.Rep.pathApply` and
`Species.Rep.IsNilpotent` already use for chains (`DEF-S5-02`, author-ratified 2026-08-30), and
`pathBimod S idx n` mentions only `idx 0, …, idx (n+1)`.  The encoding is **not injective**: two
`idx` agreeing up to `n+1` present the same path twice, so the type `Relation S` is larger than
the source's set of families.  Nothing the row claims is affected: `Satisfies` quantifies over
every `(idx, n)`, i.e. over every path together with every presentation of it, so for a family
that comes from a source relation the condition is the source's verbatim, and for an arbitrary
`R : Relation S` it is the source's condition for the path-indexed family `p ↦ ∑` of the
sub-bimodules `R` puts on the presentations of `p`.  The subcategories `Rep(S,R)` and
`Rep^nil(S,R)` cut out by the two readings are therefore the same.
-/
def Relation (S : Species K) : Type u :=
  ∀ (idx : ℕ → S.I) (n : ℕ), SubBimod (pathBimod S idx n)

/-- The zero relation — every `R_p = 0`.  @census none (G5 inhabitant of `RQ2-2.36-C3`) -/
noncomputable def Relation.bot (S : Species K) : Relation S :=
  fun idx n => SubBimod.bot (pathBimod S idx n)

/-- The maximal relation — every `R_p = {}_{i_0}M_p`.  @census none (G5 inhabitant of
`RQ2-2.36-C3`; the non-degenerate one, see `trivialMul_not_satisfies_top`) -/
noncomputable def Relation.top (S : Species K) : Relation S :=
  fun idx n => SubBimod.top (pathBimod S idx n)

/-- Every element of a path bimodule lies in the maximal relation.  @census none (helper) -/
theorem Relation.mem_top (S : Species K) (idx : ℕ → S.I) (n : ℕ)
    (x : (pathBimod S idx n).carrier) : x ∈ (Relation.top S idx n).toSubmodule :=
  SubBimod.mem_top (pathBimod S idx n) x

/-- **G5 non-vacuity**: every `K`-species carries a relation.  @census none -/
instance (S : Species K) : Nonempty (Relation S) := ⟨Relation.bot S⟩

/-! ### `RQ2-2.36-C4`, `-C5` — satisfaction and the two subcategories -/

/-- **Clause `RQ2-2.36-C4`** — the representation `(W, f)` **satisfies** `R`:
`f_p(W_{i_0} ⊗_{L_{i_0}} R_p) = 0` for every path `p`.

The condition is stated on the **generators** `w ⊗ r` of the sub-bimodule
`W_{i_0} ⊗_{L_{i_0}} R_p ⊆ W_{i_0} ⊗_{L_{i_0}} {}_{i_0}M_p`; since `f_p` is additive and that
sub-bimodule is spanned by those generators, this is the vanishing of `f_p` on it, which is what
the source's display asserts.

@census    none (auxiliary; discharges clause `RQ2-2.36-C4` of `RQ2-2.36`)
@source    def:speciesrelations
@clauses   RQ2-2.36-C4
@imports   none
@divergence none
-/
def Satisfies (V : Rep S) (R : Relation S) : Prop :=
  ∀ (idx : ℕ → S.I) (n : ℕ) (w : V.W (idx 0)) (r : (pathBimod S idx n).carrier),
    r ∈ (R idx n).toSubmodule → pathHom S V idx n (Balanced.mk w r) = 0

/-- `R_p` is closed under the right `L_{i_n}`-action, read through satisfaction: if `(W,f)`
satisfies `R` then `f_p` kills `w ⊗ (b · r)` for every `b ∈ L_{i_n}` as well.  This is the
projection that keeps `SubBimod`'s `smul_right_mem` field live (`WORKFLOW.md` G5: no dead bundle
field) — and it is the half of "sub-bimodule" that a bare `L_{i_0}`-submodule would not give.

@census none (clause witness for `RQ2-2.36-C3`/`RQ2-2.36-C4`)
@clauses   RQ2-2.36-C3
-/
theorem Satisfies.smul_right {V : Rep S} {R : Relation S} (h : Satisfies S V R)
    (idx : ℕ → S.I) (n : ℕ) (w : V.W (idx 0)) (b : (S.L (idx (n + 1)))ᵐᵒᵖ)
    (r : (pathBimod S idx n).carrier) (hr : r ∈ (R idx n).toSubmodule) :
    pathHom S V idx n (Balanced.mk w (b • r)) = 0 :=
  h idx n w (b • r) ((R idx n).smul_right_mem b hr)

/-- **Clause `RQ2-2.36-C5`**, first half — `Rep(S,R) ⊆ Rep(S)`, the **full** subcategory of the
finite-dimensional representations satisfying `R`.  As a mathlib `ObjectProperty`, so that its
fullness is mathlib's and not a private restatement (the shape `Species.RepNil` already uses).

@census    none (auxiliary; discharges clause `RQ2-2.36-C5` of `RQ2-2.36`)
@source    def:speciesrelations
@clauses   RQ2-2.36-C5
@imports   none
@divergence none
-/
def RepRel (S : Species K) (R : Relation S) : CategoryTheory.ObjectProperty (Rep S) :=
  fun V => Satisfies S V R

/-- **Clause `RQ2-2.36-C5`**, second half — `Rep^nil(S,R) ⊆ Rep(S,R)`, the full subcategory of the
**nilpotent** ones, nilpotency being `Species.Rep.IsNilpotent` (`DEF-S5-02`, intrinsic).

@census none (clause witness for `RQ2-2.36-C5`)
@clauses   RQ2-2.36-C5
-/
def RepNilRel (S : Species K) (R : Relation S) : CategoryTheory.ObjectProperty (Rep S) :=
  fun V => V.IsNilpotent ∧ Satisfies S V R

/-- `Rep^nil(S,R)` is a subcategory of `Rep(S,R)`: the second half of clause `RQ2-2.36-C5` is a
subcategory of the first.  @census none (clause witness for `RQ2-2.36-C5`) -/
theorem RepNilRel_le (S : Species K) (R : Relation S) : RepNilRel S R ≤ RepRel S R :=
  fun _ h => h.2

/-- `Rep^nil(S,R)` is exactly `Rep(S,R) ∩ Rep^nil(S)` — the sentence clause `RQ2-2.36-C5` makes.
@census none (clause witness for `RQ2-2.36-C5`) -/
theorem RepNilRel_iff (S : Species K) (R : Relation S) (V : Rep S) :
    RepNilRel S R V ↔ (RepRel S R V ∧ Species.RepNil S V) :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- `Rep(S, 0) = Rep(S)`: the zero relation imposes nothing.
@census none (G5 non-vacuity for `RQ2-2.36-C4`) -/
theorem satisfies_bot (V : Rep S) : Satisfies S V (Relation.bot S) := by
  intro idx n w r hr
  rw [show (Relation.bot S idx n).toSubmodule = ⊥ from rfl, Submodule.mem_bot] at hr
  rw [hr, Balanced.mk_zero_right' (A' := S.L (idx 0)) (B' := S.L (idx (n + 1))), map_zero]

/-- **G5 non-vacuity**: `Rep(S,R)` is inhabited for every `S` and every `R` — the representation
`ofL`, all of whose structure maps vanish, satisfies every relation.
@census none (G5 inhabitant of `RQ2-2.36-C5`) -/
theorem ofL_satisfies (S : Species K) (R : Relation S) : Satisfies S (Rep.ofL S) R := by
  intro idx n w r _
  cases n with
  | zero => rfl
  | succ n => rfl

/-- **G5 non-degeneracy** (`WORKFLOW.md` §4/G5 item 2).  Satisfaction is a **real** condition: the
one-node species `Species.trivial K` with `W_0 = K` and `f_{00}` the multiplication
(`Species.Rep.trivialMul`, the tree's non-degenerate `RQ2-2.17` inhabitant) does **not** satisfy the
maximal relation.  Without this the whole of `RQ2-2.36` could be about nothing — every
representation in the tree satisfying every relation.

@census none (G5 non-degeneracy for `RQ2-2.36-C4`)
-/
theorem trivialMul_not_satisfies_top (K : Type u) [Field K] :
    ¬ Satisfies (Species.trivial K) (Rep.trivialMul K) (Relation.top (Species.trivial K)) := by
  intro h
  refine Rep.trivialMul_f_ne_zero K PUnit.unit PUnit.unit (Balanced.hom_ext fun w r => ?_)
  exact h (fun _ => PUnit.unit) 0 w r
    (Relation.mem_top (Species.trivial K) (fun _ => PUnit.unit) 0 r)

end Species

end RationalQuivers
