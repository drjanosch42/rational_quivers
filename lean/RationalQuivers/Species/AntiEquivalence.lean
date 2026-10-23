import RationalQuivers.Species.BaseChange
import RationalQuivers.Species.OfQuiver
import RationalQuivers.Species.ToQuiver
import RationalQuivers.Species.Restriction
import RationalQuivers.Quiver.BaseChange
import RationalQuivers.Quiver.Restriction
import RationalQuivers.Quiver.Adjunction
import Mathlib.CategoryTheory.Adjunction.Opposites

/-!
# The anti-equivalence `Γ_K ↔ S` — stage **S4**

Formalizes §2.3 of `latex/rational_quivers.tex` and the two consequences the source derives from
it. This module is owned by stage **S4** (`workflow/instrument/STAGE-MAP.tsv`, row
`module RationalQuivers.Species.AntiEquivalence S4`).

## Main definitions / results
* `RationalQuivers.RationalQuiver.orbitMap`, `.edgeOrbitMap`, `.speciesMap` — the action of `S(−)`
  on morphisms (clause `RQ2-2.13-C1`).
* `RationalQuivers.SplitSpecies` — the étale `K`-species split by `L`, the full subcategory in
  which `Γ_K(−)` is defined (clause `RQ2-2.13-H1`).
* `RationalQuivers.toSpeciesFunctor` (`S(−)`) and `RationalQuivers.toQuiverFunctor` (`Γ_K(−)`) —
  the two **contravariant** functors, clauses `RQ2-2.13-C1` and `RQ2-2.13-C2`.
* `RationalQuivers.EtaleSpecies.baseChange_trans` — transitivity of base change
  (census `RQ2-2.34`), **relocated here from `Species/BaseChange.lean`**; see below.

## Relocation of `RQ2-2.34` (`MD-S3-09`, coordinator ruling 2026-08-29) — accounting

`EtaleSpecies.baseChange_trans` was **re-sequenced from stage S3 to stage S4**: the proof route the
source itself names ("The statement is also a consequence of Proposition
`prop:quiverrestrictionbasechangeadjunction`") runs through census rows `RQ2-2.08` and `RQ2-2.13`,
both S4's. Until S4's G2 the typed statement sat physically in `Species/BaseChange.lean`, an
S3-owned module, which made it a *disclosed* cross-stage claim (`STAGE-MAP.tsv`, row
`census RQ2-2.34`). This commit closes that disclosure by moving the declaration into this
S4-owned module.

**Byte-identity.** The declaration below — docstring and statement together — is the text at
commit `b3795cd` (the relocation baseline named in the header of `Species/BaseChange.lean`),
reproduced **byte for byte**: 31 lines, 2037 bytes,
`sha256 a1527d25c9ccd92a8dce6a1b96d359e44132f4f1fcda59974305be19a4993afc`. The section `variable`
block below reproduces `Species/BaseChange.lean`'s verbatim, so the *elaborated* signature is
unchanged as well; that is the check that matters (`CONVENTIONS.md` §3: confirm from the
environment, never from the source text), and it is recorded in
`workflow/stages/S4/RELOCATION-RQ2-2.34.md`.

**No-discharge accounting.** The move discharges **nothing**. The `sorry` moves with the statement:
the project's `sorry` count is unchanged by this commit, `RQ2-2.34` remains unproved, and the
`@divergence` disclosure (finding V-2 of the S3 G2 verification) travels with the docstring
unaltered. What changes is *only* the owning module, hence the stage attribution
`rqaudit coverage` computes for the row. The S4 proof, and the named `def baseChangeTransIso` that
V-2 asks for, land later in this stage.

**G4 addendum (2026-08-31): the declaration is now proved, and what that cost the byte-identity.**
The relocation baseline is 31 lines / 2037 bytes,
`sha256 a1527d25c9ccd92a8dce6a1b96d359e44132f4f1fcda59974305be19a4993afc` — and those 31 lines
*include the two-line `sorry` body*. Discharging `RQ2-2.34` therefore necessarily changes 15 of the
2037 bytes: the body ` := by\n  sorry\n` became the proof. **Docstring and statement are
unchanged, byte for byte**: the first 2022 bytes, ending at
`Function.Bijective (CategoryTheory.Iso.hom e).onI`, are
`sha256 f898a1d2a56913cfa34ff6abbc3b0d9fbbd4cfb0d3becebcb90b31763ddaafb4`, measured against
`b3795cd:lean/RationalQuivers/Species/BaseChange.lean`. The elaborated signature is unchanged too
(checked from the environment, `CONVENTIONS.md` §3): the section `variable` block still precedes
the declaration verbatim. The declaration has also moved **within this module**, from the head to
after the `RQ2-2.34` machinery, because its proof consumes that machinery; the owning module, which
is what `rqaudit coverage` reads, is unchanged.

**The route the `@divergence` names is not available, and this is the disclosure of that.** The
field says the proof "goes through `prop:speciesrestrictionbasechangeadjunction` and the
anti-equivalence (`RQ2-2.08`, `RQ2-2.13`)". It cannot: `baseChange_trans` quantifies over **arbitrary**
field extensions `N'/N/K` — no finiteness, no separability, no intermediate field — whereas
`RQ2-2.13` and both agreement theorems of `RQ2-2.08` are defined only for an
`E' : IntermediateField K L` with `L/K` finite Galois and the species split by `L`. `K = ℚ`,
`N = ℚ(t)`, `N' = ℚ(t,s)` lies in this statement's domain and outside theirs. The proof below takes
instead the direct route `ledger/MATHLIB-DECISIONS.tsv` `MD-S3-09` anticipated, whose missing
ingredient — uniqueness of the decomposition of a finite étale algebra into fields — is
`PiSplit.splitting_match`. Nothing about the *statement* changes; only the `@divergence` field's
last sentence is superseded, and it is superseded here rather than silently.
-/

universe u

namespace RationalQuivers

open scoped TensorProduct
open CategoryTheory


/-! ## The functor `S(−)` on morphisms (clause `RQ2-2.13-C1`)

`S(−)` is **contravariant**: a morphism `f : Γ ⟶ Γ'` of `K`-rational quivers induces
`S(f) : S(Γ') ⟶ S(Γ)`. Its index component is the orbit map `I(Γ) → I(Γ')` that `f` induces, and
its algebra components run the other way, `L'_{φ(i)} → L_i` — because `G_v ⊆ G_{f(v)}` makes the
fixed field *shrink* along `f`. That mismatch of directions is finding **S4-F1**; it is what the
amended `RQ2-2.04` accommodates (see `Species/Hom.lean`'s `@divergence` and the two witnesses in
`Species/Examples.lean`).
-/

namespace RationalQuiver

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  {Γ Γ' : RationalQuiver K L}

open MulAction

/-- The stabilizer of a vertex is contained in the stabilizer of its image: a morphism of
`K`-rational quivers is `Gal(L/K)`-equivariant, so `σ v = v` forces `σ (f v) = f v`. This is what
makes `L(f v) ⊆ L(v)`, i.e. what makes the algebra components of `S(f)` run against its index
component.

@census none (helper for clause `RQ2-2.13-C1`)
-/
theorem stabilizer_le_onV (f : Γ ⟶ Γ') (v : Γ.V) :
    stabilizer Gal(L/K) v ≤ stabilizer Gal(L/K) (f.toRQuiverHom.onV v) := by
  intro σ hσ
  rw [mem_stabilizer_iff] at hσ ⊢
  rw [← f.equivariant_V, hσ]

/-- Likewise for edges. -/
theorem stabilizer_le_onE (f : Γ ⟶ Γ') (e : Γ.E) :
    stabilizer Gal(L/K) e ≤ stabilizer Gal(L/K) (f.toRQuiverHom.onE e) := by
  intro σ hσ
  rw [mem_stabilizer_iff] at hσ ⊢
  rw [← f.equivariant_E, hσ]

/-- `L(f v) ⊆ L(v)`. -/
theorem stabField_onV_le (f : Γ ⟶ Γ') (v : Γ.V) :
    stabField K L (f.toRQuiverHom.onV v) ≤ stabField K L v :=
  IntermediateField.fixedField_le (stabilizer_le_onV f v)

/-- `L(f e) ⊆ L(e)`. -/
theorem stabField_onE_le (f : Γ ⟶ Γ') (e : Γ.E) :
    stabField K L (f.toRQuiverHom.onE e) ≤ stabField K L e :=
  IntermediateField.fixedField_le (stabilizer_le_onE f e)

/-- **Clause `RQ2-2.13-C1`, index component.** The map `I(Γ) → I(Γ')` of orbit sets induced by a
morphism of `K`-rational quivers. Well defined because `f` is `Gal(L/K)`-equivariant, so it carries
orbits into orbits.

@census none (clause witness for `RQ2-2.13-C1`)
-/
def orbitMap (f : Γ ⟶ Γ') : Γ.VertexOrbit → Γ'.VertexOrbit :=
  Quotient.lift (fun v => Γ'.vertexClass (f.toRQuiverHom.onV v)) <| by
    intro v w h
    obtain ⟨σ, rfl⟩ := mem_orbit_iff.mp h
    exact Quotient.sound (by rw [f.equivariant_V]; exact mem_orbit _ σ)

@[simp] theorem orbitMap_vertexClass (f : Γ ⟶ Γ') (v : Γ.V) :
    orbitMap f (Γ.vertexClass v) = Γ'.vertexClass (f.toRQuiverHom.onV v) := rfl

/-- A morphism carries `E_{ij}` into `E_{φ(i)φ(j)}`: `s` and `t` commute with `f`, and orbits are
carried to orbits.

@census none (helper for clause `RQ2-2.13-C1`)
-/
theorem onE_mem_edgeSet (f : Γ ⟶ Γ') {i j : Γ.VertexOrbit} (e : Γ.edgeSet i j) :
    f.toRQuiverHom.onE (e : Γ.E) ∈ Γ'.edgeSet (orbitMap f i) (orbitMap f j) := by
  constructor
  · calc Γ'.vertexClass (Γ'.toRQuiver.source (f.toRQuiverHom.onE (e : Γ.E)))
        = Γ'.vertexClass (f.toRQuiverHom.onV (Γ.toRQuiver.source (e : Γ.E))) := by
          rw [f.toRQuiverHom.onV_source]
      _ = orbitMap f (Γ.vertexClass (Γ.toRQuiver.source (e : Γ.E))) := rfl
      _ = orbitMap f i := by rw [e.2.1]
  · calc Γ'.vertexClass (Γ'.toRQuiver.target (f.toRQuiverHom.onE (e : Γ.E)))
        = Γ'.vertexClass (f.toRQuiverHom.onV (Γ.toRQuiver.target (e : Γ.E))) := by
          rw [f.toRQuiverHom.onV_target]
      _ = orbitMap f (Γ.vertexClass (Γ.toRQuiver.target (e : Γ.E))) := rfl
      _ = orbitMap f j := by rw [e.2.2]

/-- **Clause `RQ2-2.13-C1`, edge-index component.** The induced map on edge orbits.

@census none (clause witness for `RQ2-2.13-C1`)
-/
def edgeOrbitMap (f : Γ ⟶ Γ') {i j : Γ.VertexOrbit} :
    Γ.EdgeOrbit i j → Γ'.EdgeOrbit (orbitMap f i) (orbitMap f j) :=
  Quotient.lift (fun e => Quotient.mk (orbitRel Gal(L/K) _)
      (⟨f.toRQuiverHom.onE (e : Γ.E), onE_mem_edgeSet f e⟩ :
        Γ'.edgeSet (orbitMap f i) (orbitMap f j))) <| by
    intro e e' h
    obtain ⟨σ, hσ⟩ := mem_orbit_iff.mp h
    refine Quotient.sound ⟨σ, Subtype.ext ?_⟩
    show σ • f.toRQuiverHom.onE ((e' : Γ.edgeSet i j) : Γ.E)
        = f.toRQuiverHom.onE ((e : Γ.edgeSet i j) : Γ.E)
    rw [← f.equivariant_E]
    exact congrArg _ (congrArg Subtype.val hσ)

/-- The image of the chosen representative `v_i` lies in the orbit `φ(i)`, hence in the orbit of
that orbit's own chosen representative — the step that produces the algebra component of `S(f)`.

@census none (helper for clause `RQ2-2.13-C1`)
-/
theorem onV_vertexRep_mem_orbit (f : Γ ⟶ Γ') (i : Γ.VertexOrbit) :
    f.toRQuiverHom.onV (Γ.vertexRep i) ∈ orbit Gal(L/K) (Γ'.vertexRep (orbitMap f i)) :=
  by
  have h : Γ'.vertexClass (f.toRQuiverHom.onV (Γ.vertexRep i))
      = Γ'.vertexClass (Γ'.vertexRep (orbitMap f i)) := by
    rw [Γ'.vertexClass_vertexRep, ← orbitMap_vertexClass, Γ.vertexClass_vertexRep]
  exact Quotient.exact h

/-- The edge analogue of `onV_vertexRep_mem_orbit`.

@census none (helper for clause `RQ2-2.13-C1`)
-/
theorem onE_edgeRep_mem_orbit (f : Γ ⟶ Γ') {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) :
    f.toRQuiverHom.onE (Γ.edgeRep ε) ∈ orbit Gal(L/K) (Γ'.edgeRep (edgeOrbitMap f ε)) := by
  have hx : Quotient.mk (orbitRel Gal(L/K) (Γ'.edgeSet (orbitMap f i) (orbitMap f j)))
      ⟨f.toRQuiverHom.onE (Γ.edgeRep ε), onE_mem_edgeSet f (Quotient.out ε)⟩
      = edgeOrbitMap f ε := by
    conv_rhs => rw [← Quotient.out_eq ε]
    rfl
  have h := Γ'.mem_orbit_edgeRep
    (⟨f.toRQuiverHom.onE (Γ.edgeRep ε), onE_mem_edgeSet f (Quotient.out ε)⟩ :
      Γ'.edgeSet (orbitMap f i) (orbitMap f j))
  rwa [hx] at h

/-- **Clause `RQ2-2.13-C1`, vertex-algebra component.** `L'_{φ(i)} → L_i`. -/
noncomputable def speciesMapOnL (f : Γ ⟶ Γ') (i : Γ.VertexOrbit) :
    Γ'.vertexOrbitField (orbitMap f i) →ₐ[K] Γ.vertexOrbitField i :=
  (IntermediateField.inclusion (stabField_onV_le f (Γ.vertexRep i))).comp
    (stabFieldEquivOrbit (onV_vertexRep_mem_orbit f i)).toAlgHom

/-- **Clause `RQ2-2.13-C1`, edge-algebra component**, on the `ε`-summand. -/
noncomputable def speciesMapOnEdgeField (f : Γ ⟶ Γ') {i j : Γ.VertexOrbit}
    (ε : Γ.EdgeOrbit i j) :
    Γ'.edgeOrbitField (edgeOrbitMap f ε) →ₐ[K] Γ.edgeOrbitField ε :=
  (IntermediateField.inclusion (stabField_onE_le f (Γ.edgeRep ε))).comp
    (stabFieldEquivOrbit (onE_edgeRep_mem_orbit f ε)).toAlgHom

noncomputable def speciesMapOnM (f : Γ ⟶ Γ') (s t : Γ.VertexOrbit) :
    Γ'.toSpecies.M (orbitMap f s) (orbitMap f t) →ₐ[K] Γ.toSpecies.M s t :=
  Pi.algHom K _ fun ε => (speciesMapOnEdgeField f ε).comp (Pi.evalAlgHom K _ (edgeOrbitMap f ε))

/-- Compatibility of `S(f)`'s edge component with the **left** structure maps (clause `RQ2-2.04-C3`
for the morphism `S(f)`).

Proof plan (G4): componentwise at an edge orbit `ε`, both sides send `α ∈ L'_{φ(i)}` to `σ α` for a
group element `σ` carrying the chosen representative of `φ(ε)` to the image of the chosen
representative of `ε`; `stabField_apply_eq_of_smul_eq` identifies the two choices.

@census none (clause witness for `RQ2-2.13-C1`)
-/
theorem speciesMap_compat_left (f : Γ ⟶ Γ') (s t : Γ.VertexOrbit) :
    (speciesMapOnM f s t).comp (Γ'.toSpecies.left (orbitMap f s) (orbitMap f t))
      = (Γ.toSpecies.left s t).comp (speciesMapOnL f s) := by
  refine AlgHom.ext fun α => ?_
  refine funext fun ε => ?_
  set ρ' := (mem_orbit_iff.mp (onE_edgeRep_mem_orbit f ε)).choose
  set σ'' := (mem_orbit_iff.mp (Γ'.source_edgeRep_mem_orbit (edgeOrbitMap f ε))).choose
  set σ₃ := (mem_orbit_iff.mp (Γ.source_edgeRep_mem_orbit ε)).choose
  set σ₄ := (mem_orbit_iff.mp (onV_vertexRep_mem_orbit f s)).choose
  have eρ' : ρ' • Γ'.edgeRep (edgeOrbitMap f ε) = f.toRQuiverHom.onE (Γ.edgeRep ε) :=
    (mem_orbit_iff.mp (onE_edgeRep_mem_orbit f ε)).choose_spec
  have eσ'' : σ'' • Γ'.vertexRep (orbitMap f s)
      = Γ'.toRQuiver.source (Γ'.edgeRep (edgeOrbitMap f ε)) :=
    (mem_orbit_iff.mp (Γ'.source_edgeRep_mem_orbit (edgeOrbitMap f ε))).choose_spec
  have eσ₃ : σ₃ • Γ.vertexRep s = Γ.toRQuiver.source (Γ.edgeRep ε) :=
    (mem_orbit_iff.mp (Γ.source_edgeRep_mem_orbit ε)).choose_spec
  have eσ₄ : σ₄ • Γ'.vertexRep (orbitMap f s) = f.toRQuiverHom.onV (Γ.vertexRep s) :=
    (mem_orbit_iff.mp (onV_vertexRep_mem_orbit f s)).choose_spec
  have key : (ρ' * σ'') • Γ'.vertexRep (orbitMap f s)
      = (σ₃ * σ₄) • Γ'.vertexRep (orbitMap f s) := by
    rw [mul_smul, mul_smul, eσ'', eσ₄, ← Γ'.source_smul, eρ', ← f.equivariant_V, eσ₃,
      f.toRQuiverHom.onV_source]
  exact Subtype.ext (stabField_apply_eq_of_smul_eq (σ := ρ' * σ'') (τ := σ₃ * σ₄) key α)

/-- Compatibility of `S(f)`'s edge component with the **right** structure maps.

@census none (clause witness for `RQ2-2.13-C1`)
-/
theorem speciesMap_compat_right (f : Γ ⟶ Γ') (s t : Γ.VertexOrbit) :
    (speciesMapOnM f s t).comp (Γ'.toSpecies.right (orbitMap f s) (orbitMap f t))
      = (Γ.toSpecies.right s t).comp (speciesMapOnL f t) := by
  refine AlgHom.ext fun α => ?_
  refine funext fun ε => ?_
  set ρ' := (mem_orbit_iff.mp (onE_edgeRep_mem_orbit f ε)).choose
  set σ'' := (mem_orbit_iff.mp (Γ'.target_edgeRep_mem_orbit (edgeOrbitMap f ε))).choose
  set σ₃ := (mem_orbit_iff.mp (Γ.target_edgeRep_mem_orbit ε)).choose
  set σ₄ := (mem_orbit_iff.mp (onV_vertexRep_mem_orbit f t)).choose
  have eρ' : ρ' • Γ'.edgeRep (edgeOrbitMap f ε) = f.toRQuiverHom.onE (Γ.edgeRep ε) :=
    (mem_orbit_iff.mp (onE_edgeRep_mem_orbit f ε)).choose_spec
  have eσ'' : σ'' • Γ'.vertexRep (orbitMap f t)
      = Γ'.toRQuiver.target (Γ'.edgeRep (edgeOrbitMap f ε)) :=
    (mem_orbit_iff.mp (Γ'.target_edgeRep_mem_orbit (edgeOrbitMap f ε))).choose_spec
  have eσ₃ : σ₃ • Γ.vertexRep t = Γ.toRQuiver.target (Γ.edgeRep ε) :=
    (mem_orbit_iff.mp (Γ.target_edgeRep_mem_orbit ε)).choose_spec
  have eσ₄ : σ₄ • Γ'.vertexRep (orbitMap f t) = f.toRQuiverHom.onV (Γ.vertexRep t) :=
    (mem_orbit_iff.mp (onV_vertexRep_mem_orbit f t)).choose_spec
  have key : (ρ' * σ'') • Γ'.vertexRep (orbitMap f t)
      = (σ₃ * σ₄) • Γ'.vertexRep (orbitMap f t) := by
    rw [mul_smul, mul_smul, eσ'', eσ₄, ← Γ'.target_smul, eρ', ← f.equivariant_V, eσ₃,
      f.toRQuiverHom.onV_target]
  exact Subtype.ext (stabField_apply_eq_of_smul_eq (σ := ρ' * σ'') (τ := σ₃ * σ₄) key α)

/-- **Clause `RQ2-2.13-C1`.** The morphism `S(f) : S(Γ') ⟶ S(Γ)` of étale `K`-species induced by a
morphism `f : Γ ⟶ Γ'` of `K`-rational quivers: the index component is the orbit map `I(Γ) → I(Γ')`,
and the algebra components run against it, `L'_{φ(i)} → L_i` and
`{}_{φ(i)}M'_{φ(j)} → {}_iM_j`, the latter by projecting to the `φ`-image edge orbit and then
including. This is exactly the shape the amended `RQ2-2.04` provides (finding S4-F1).

@census none (clause witness for `RQ2-2.13-C1`)
-/
noncomputable def speciesMap (f : Γ ⟶ Γ') : Γ'.toSpecies ⟶ Γ.toSpecies where
  onI := orbitMap f
  onL := speciesMapOnL f
  onM := speciesMapOnM f
  compat_left := speciesMap_compat_left f
  compat_right := speciesMap_compat_right f

/-! ### The dependent-transport toolkit (functoriality of `S(−)`)

Functoriality is where the `Sigma`/`HEq` transport S3 predicted for `RQ2-2.34` actually bites: the
index component of `S(𝟙)` is `orbitMap (𝟙 Γ)`, which is *pointwise* the identity but is not the
identity function on the nose (it is `Quotient.lift Quotient.mk`), and the algebra components are
indexed by it. `EtaleSpecies.Hom.ext` therefore hands out `HEq` goals.

The five lemmas below are the whole of the transport. Each one takes the index equalities as
hypotheses about **variables**, so that a single `cases` aligns the types; the consumer then works
with ordinary equations in `L`. This is the same discipline as `vertexSet_ext_of_val` below —
*dependent types are handled by descending to `L`, not by transporting* — and it is what keeps
`speciesMap_id`, `speciesMap_comp` and the `Γ_K(−)` functoriality proofs free of `▸`.
-/

/-- Two `K`-algebra maps out of intermediate fields agree (`HEq`) as soon as the fields agree and
the maps agree on underlying elements of `L`.

@census none (transport helper for clause `RQ2-2.13-C1`)
-/
theorem heq_algHom_of_val {E F : IntermediateField K L} {A : Type u} [Semiring A] [Algebra K A]
    {φ : E →ₐ[K] A} {ψ : F →ₐ[K] A} (h : E = F)
    (h2 : ∀ (a : L) (ha : a ∈ E) (hb : a ∈ F), φ ⟨a, ha⟩ = ψ ⟨a, hb⟩) : HEq φ ψ := by
  cases h
  exact heq_of_eq (AlgHom.ext fun x => h2 x x.2 x.2)

/-- The edge-algebra analogue of `heq_algHom_of_val`: the index equalities align the two products
`{}_iM_j`, after which the maps are compared on `HEq`-related arguments.

@census none (transport helper for clause `RQ2-2.13-C1`)
-/
theorem heq_algHom_edgeAlgebra {s₁ s₂ t₁ t₂ : Γ.VertexOrbit} (hs : s₁ = s₂) (ht : t₁ = t₂)
    {A : Type u} [Semiring A] [Algebra K A]
    {φ : Γ.edgeAlgebra s₁ t₁ →ₐ[K] A} {ψ : Γ.edgeAlgebra s₂ t₂ →ₐ[K] A}
    (h : ∀ (x : Γ.edgeAlgebra s₁ t₁) (y : Γ.edgeAlgebra s₂ t₂), HEq x y → φ x = ψ y) :
    HEq φ ψ := by
  cases hs; cases ht
  exact heq_of_eq (AlgHom.ext fun x => h x x HEq.rfl)

/-- An edge sitting in two (equal) edge sets has the same orbit class in both.

@census none (transport helper for clause `RQ2-2.13-C1`)
-/
theorem heq_edgeOrbit_mk {s₁ s₂ t₁ t₂ : Γ.VertexOrbit} (hs : s₁ = s₂) (ht : t₁ = t₂)
    (e : Γ.E) (h₁ : e ∈ Γ.edgeSet s₁ t₁) (h₂ : e ∈ Γ.edgeSet s₂ t₂) :
    HEq (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet s₁ t₁)) ⟨e, h₁⟩)
        (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet s₂ t₂)) ⟨e, h₂⟩) := by
  cases hs; cases ht; rfl

/-- The `σ`-translate of an edge has the same orbit class — the edge form of
`Quotient.sound (mem_orbit _ σ)`, carried across the index equality.

@census none (transport helper for clause `RQ2-2.13-C3`)
-/
theorem heq_edgeOrbit_mk_smul {s₁ s₂ t₁ t₂ : Γ.VertexOrbit} (hs : s₁ = s₂) (ht : t₁ = t₂)
    (σ : Gal(L/K)) (e : Γ.E) (h₁ : σ • e ∈ Γ.edgeSet s₁ t₁) (h₂ : e ∈ Γ.edgeSet s₂ t₂) :
    HEq (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet s₁ t₁)) ⟨σ • e, h₁⟩)
        (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet s₂ t₂)) ⟨e, h₂⟩) := by
  cases hs; cases ht
  exact heq_of_eq (Quotient.sound (mem_orbit (⟨e, h₂⟩ : Γ.edgeSet _ _) σ))

/-- `HEq`-related edge orbits have the *same* chosen representative — an equation in `Γ.E`, which
is where the transport stops.

@census none (transport helper for clause `RQ2-2.13-C1`)
-/
theorem edgeRep_heq_congr {s₁ s₂ t₁ t₂ : Γ.VertexOrbit} (hs : s₁ = s₂) (ht : t₁ = t₂)
    {ε₁ : Γ.EdgeOrbit s₁ t₁} {ε₂ : Γ.EdgeOrbit s₂ t₂} (h : HEq ε₁ ε₂) :
    Γ.edgeRep ε₁ = Γ.edgeRep ε₂ := by
  cases hs; cases ht; cases h; rfl

/-- `HEq`-related elements of `{}_iM_j` have equal components, as elements of `L`, at
`HEq`-related edge orbits.

@census none (transport helper for clause `RQ2-2.13-C1`)
-/
theorem edgeAlgebra_apply_val_congr {s₁ s₂ t₁ t₂ : Γ.VertexOrbit} (hs : s₁ = s₂) (ht : t₁ = t₂)
    {x : Γ.edgeAlgebra s₁ t₁} {y : Γ.edgeAlgebra s₂ t₂} (hxy : HEq x y)
    {ε₁ : Γ.EdgeOrbit s₁ t₁} {ε₂ : Γ.EdgeOrbit s₂ t₂} (hε : HEq ε₁ ε₂) :
    ((x ε₁ : L)) = (y ε₂ : L) := by
  cases hs; cases ht; cases hxy; cases hε; rfl

/-- The value of `S(f)`'s vertex component in `L`: the chosen group element applied to the
argument. Every functoriality computation below runs through this equation.

@census none (transport helper for clause `RQ2-2.13-C1`)
-/
theorem speciesMapOnL_coe (f : Γ ⟶ Γ') (i : Γ.VertexOrbit)
    (a : Γ'.vertexOrbitField (orbitMap f i)) :
    ((speciesMapOnL f i a : Γ.vertexOrbitField i) : L)
      = (mem_orbit_iff.mp (onV_vertexRep_mem_orbit f i)).choose (a : L) := by
  have h : speciesMapOnL f i a
      = IntermediateField.inclusion (stabField_onV_le f (Γ.vertexRep i))
          (stabFieldEquivOrbit (onV_vertexRep_mem_orbit f i) a) := rfl
  rw [h, IntermediateField.coe_inclusion, stabFieldEquivOrbit_coe]

/-- The edge analogue of `speciesMapOnL_coe`.

@census none (transport helper for clause `RQ2-2.13-C1`)
-/
theorem speciesMapOnEdgeField_coe (f : Γ ⟶ Γ') {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (a : Γ'.edgeOrbitField (edgeOrbitMap f ε)) :
    ((speciesMapOnEdgeField f ε a : Γ.edgeOrbitField ε) : L)
      = (mem_orbit_iff.mp (onE_edgeRep_mem_orbit f ε)).choose (a : L) := by
  have h : speciesMapOnEdgeField f ε a
      = IntermediateField.inclusion (stabField_onE_le f (Γ.edgeRep ε))
          (stabFieldEquivOrbit (onE_edgeRep_mem_orbit f ε) a) := rfl
  rw [h, IntermediateField.coe_inclusion, stabFieldEquivOrbit_coe]

/-- `orbitMap` is pointwise the identity on `𝟙` — but only pointwise: `orbitMap (𝟙 Γ)` is
`Quotient.lift Quotient.mk`, not `id`, which is the whole source of the transport below.

@census none (transport helper for clause `RQ2-2.13-C1`)
-/
theorem orbitMap_id_apply (Γ : RationalQuiver K L) (i : Γ.VertexOrbit) :
    orbitMap (𝟙 Γ) i = i := Quotient.inductionOn i fun _ => rfl

/-- `orbitMap` is pointwise functorial. -/
theorem orbitMap_comp_apply {Γ'' : RationalQuiver K L} (f : Γ ⟶ Γ') (g : Γ' ⟶ Γ'')
    (i : Γ.VertexOrbit) : orbitMap (f ≫ g) i = orbitMap g (orbitMap f i) :=
  Quotient.inductionOn i fun _ => rfl

/-- The edge-orbit map of `𝟙` is the identity, up to the index transport. -/
theorem heq_edgeOrbitMap_id {s t : Γ.VertexOrbit} (ε : Γ.EdgeOrbit s t) :
    HEq (edgeOrbitMap (𝟙 Γ) ε) ε := by
  refine Quotient.inductionOn ε fun x => ?_
  exact heq_edgeOrbit_mk (orbitMap_id_apply Γ s) (orbitMap_id_apply Γ t) (x : Γ.E) _ x.2

/-- The edge-orbit map is functorial, up to the index transport. -/
theorem heq_edgeOrbitMap_comp {Γ'' : RationalQuiver K L} (f : Γ ⟶ Γ') (g : Γ' ⟶ Γ'')
    {s t : Γ.VertexOrbit} (ε : Γ.EdgeOrbit s t) :
    HEq (edgeOrbitMap (f ≫ g) ε) (edgeOrbitMap g (edgeOrbitMap f ε)) := by
  refine Quotient.inductionOn ε fun x => ?_
  exact heq_edgeOrbit_mk (orbitMap_comp_apply f g s) (orbitMap_comp_apply f g t) _ _ _

/-- The vertex component of `S(𝟙)` is the identity. Both sides send `a` to `σ a` for a `σ` fixing
the chosen representative, so `stabField_apply_eq_of_smul_eq` (with `τ = 1`) closes it.

@census none (clause witness for `RQ2-2.13-C1`)
-/
theorem speciesMapOnL_heq_id (Γ : RationalQuiver K L) (i : Γ.VertexOrbit) :
    HEq (speciesMapOnL (𝟙 Γ) i) (AlgHom.id K (Γ.vertexOrbitField i)) := by
  refine heq_algHom_of_val (congrArg Γ.vertexOrbitField (orbitMap_id_apply Γ i)) ?_
  intro a ha hb
  refine Subtype.ext ?_
  show ((stabFieldEquivOrbit (onV_vertexRep_mem_orbit (𝟙 Γ) i)) ⟨a, ha⟩ : L) = a
  rw [stabFieldEquivOrbit_coe]
  have hspec := (mem_orbit_iff.mp (onV_vertexRep_mem_orbit (𝟙 Γ) i)).choose_spec
  have hx : (mem_orbit_iff.mp (onV_vertexRep_mem_orbit (𝟙 Γ) i)).choose
        • Γ.vertexRep (orbitMap (𝟙 Γ) i)
      = (1 : Gal(L/K)) • Γ.vertexRep (orbitMap (𝟙 Γ) i) := by
    rw [one_smul, hspec]
    show Γ.vertexRep i = Γ.vertexRep (orbitMap (𝟙 Γ) i)
    rw [orbitMap_id_apply Γ i]
  simpa using stabField_apply_eq_of_smul_eq hx ⟨a, ha⟩

/-- The edge component of `S(𝟙)` is the identity.

@census none (clause witness for `RQ2-2.13-C1`)
-/
theorem speciesMapOnM_heq_id (Γ : RationalQuiver K L) (s t : Γ.VertexOrbit) :
    HEq (speciesMapOnM (𝟙 Γ) s t) (AlgHom.id K (Γ.edgeAlgebra s t)) := by
  refine heq_algHom_edgeAlgebra (orbitMap_id_apply Γ s) (orbitMap_id_apply Γ t) ?_
  intro x y hxy
  funext ε
  refine Subtype.ext ?_
  show ((stabFieldEquivOrbit (onE_edgeRep_mem_orbit (𝟙 Γ) ε))
      (x (edgeOrbitMap (𝟙 Γ) ε)) : L) = (y ε : L)
  rw [stabFieldEquivOrbit_coe]
  have hrep : Γ.edgeRep (edgeOrbitMap (𝟙 Γ) ε) = Γ.edgeRep ε :=
    edgeRep_heq_congr (orbitMap_id_apply Γ s) (orbitMap_id_apply Γ t) (heq_edgeOrbitMap_id ε)
  have hspec := (mem_orbit_iff.mp (onE_edgeRep_mem_orbit (𝟙 Γ) ε)).choose_spec
  have hx : (mem_orbit_iff.mp (onE_edgeRep_mem_orbit (𝟙 Γ) ε)).choose
        • Γ.edgeRep (edgeOrbitMap (𝟙 Γ) ε)
      = (1 : Gal(L/K)) • Γ.edgeRep (edgeOrbitMap (𝟙 Γ) ε) := by
    rw [one_smul, hspec, hrep]
    rfl
  have hfix := stabField_apply_eq_of_smul_eq hx (x (edgeOrbitMap (𝟙 Γ) ε))
  rw [show ((1 : Gal(L/K)) : L ≃ₐ[K] L) = AlgEquiv.refl from rfl] at hfix
  rw [hfix]
  exact edgeAlgebra_apply_val_congr (orbitMap_id_apply Γ s) (orbitMap_id_apply Γ t) hxy
    (heq_edgeOrbitMap_id ε)

/-- The vertex component of `S(−)` is functorial: both sides are the action of a group element
carrying the chosen representative of the composite orbit to the image of the representative, and
the two elements agree by `stabField_apply_eq_of_smul_eq`.

@census none (clause witness for `RQ2-2.13-C1`)
-/
theorem speciesMapOnL_heq_comp {Γ'' : RationalQuiver K L} (f : Γ ⟶ Γ') (g : Γ' ⟶ Γ'')
    (i : Γ.VertexOrbit) :
    HEq (speciesMapOnL (f ≫ g) i) ((speciesMapOnL f i).comp (speciesMapOnL g (orbitMap f i))) := by
  refine heq_algHom_of_val (congrArg Γ''.vertexOrbitField (orbitMap_comp_apply f g i)) ?_
  intro a ha hb
  refine Subtype.ext ?_
  simp only [AlgHom.comp_apply, speciesMapOnL_coe]
  have hf := (mem_orbit_iff.mp (onV_vertexRep_mem_orbit f i)).choose_spec
  have hg := (mem_orbit_iff.mp (onV_vertexRep_mem_orbit g (orbitMap f i))).choose_spec
  have hfg := (mem_orbit_iff.mp (onV_vertexRep_mem_orbit (f ≫ g) i)).choose_spec
  have key : (mem_orbit_iff.mp (onV_vertexRep_mem_orbit (f ≫ g) i)).choose
        • Γ''.vertexRep (orbitMap (f ≫ g) i)
      = ((mem_orbit_iff.mp (onV_vertexRep_mem_orbit f i)).choose *
          (mem_orbit_iff.mp (onV_vertexRep_mem_orbit g (orbitMap f i))).choose)
        • Γ''.vertexRep (orbitMap (f ≫ g) i) := by
    rw [hfg, mul_smul]
    rw [show Γ''.vertexRep (orbitMap (f ≫ g) i)
        = Γ''.vertexRep (orbitMap g (orbitMap f i)) from
      congrArg Γ''.vertexRep (orbitMap_comp_apply f g i)]
    rw [hg, ← g.equivariant_V, hf]
    rfl
  simpa using stabField_apply_eq_of_smul_eq key ⟨a, ha⟩

/-- The edge component of `S(−)` is functorial.

@census none (clause witness for `RQ2-2.13-C1`)
-/
theorem speciesMapOnM_heq_comp {Γ'' : RationalQuiver K L} (f : Γ ⟶ Γ') (g : Γ' ⟶ Γ'')
    (s t : Γ.VertexOrbit) :
    HEq (speciesMapOnM (f ≫ g) s t)
      ((speciesMapOnM f s t).comp (speciesMapOnM g (orbitMap f s) (orbitMap f t))) := by
  refine heq_algHom_edgeAlgebra (orbitMap_comp_apply f g s) (orbitMap_comp_apply f g t) ?_
  intro x y hxy
  funext ε
  have e1 : ((speciesMapOnM (f ≫ g) s t x ε : Γ.edgeOrbitField ε) : L)
      = (mem_orbit_iff.mp (onE_edgeRep_mem_orbit (f ≫ g) ε)).choose
          (x (edgeOrbitMap (f ≫ g) ε) : L) :=
    speciesMapOnEdgeField_coe (f ≫ g) ε (x (edgeOrbitMap (f ≫ g) ε))
  have e2 : ((((speciesMapOnM f s t).comp
        (speciesMapOnM g (orbitMap f s) (orbitMap f t))) y ε : Γ.edgeOrbitField ε) : L)
      = (mem_orbit_iff.mp (onE_edgeRep_mem_orbit f ε)).choose
          ((speciesMapOnEdgeField g (edgeOrbitMap f ε)
            (y (edgeOrbitMap g (edgeOrbitMap f ε))) : Γ'.edgeOrbitField (edgeOrbitMap f ε)) : L) :=
    speciesMapOnEdgeField_coe f ε _
  have e3 : ((speciesMapOnEdgeField g (edgeOrbitMap f ε)
        (y (edgeOrbitMap g (edgeOrbitMap f ε))) : Γ'.edgeOrbitField (edgeOrbitMap f ε)) : L)
      = (mem_orbit_iff.mp (onE_edgeRep_mem_orbit g (edgeOrbitMap f ε))).choose
          (y (edgeOrbitMap g (edgeOrbitMap f ε)) : L) :=
    speciesMapOnEdgeField_coe g (edgeOrbitMap f ε) _
  have e23 : ((((speciesMapOnM f s t).comp
        (speciesMapOnM g (orbitMap f s) (orbitMap f t))) y ε : Γ.edgeOrbitField ε) : L)
      = (mem_orbit_iff.mp (onE_edgeRep_mem_orbit f ε)).choose
          ((mem_orbit_iff.mp (onE_edgeRep_mem_orbit g (edgeOrbitMap f ε))).choose
            (y (edgeOrbitMap g (edgeOrbitMap f ε)) : L)) := by
    rw [e2, e3]
  have hval : ((x (edgeOrbitMap (f ≫ g) ε) : L))
      = (y (edgeOrbitMap g (edgeOrbitMap f ε)) : L) :=
    edgeAlgebra_apply_val_congr (orbitMap_comp_apply f g s) (orbitMap_comp_apply f g t) hxy
      (heq_edgeOrbitMap_comp f g ε)
  have hf := (mem_orbit_iff.mp (onE_edgeRep_mem_orbit f ε)).choose_spec
  have hg := (mem_orbit_iff.mp (onE_edgeRep_mem_orbit g (edgeOrbitMap f ε))).choose_spec
  have hfg := (mem_orbit_iff.mp (onE_edgeRep_mem_orbit (f ≫ g) ε)).choose_spec
  have hrep : Γ''.edgeRep (edgeOrbitMap (f ≫ g) ε)
      = Γ''.edgeRep (edgeOrbitMap g (edgeOrbitMap f ε)) :=
    edgeRep_heq_congr (orbitMap_comp_apply f g s) (orbitMap_comp_apply f g t)
      (heq_edgeOrbitMap_comp f g ε)
  have key : (mem_orbit_iff.mp (onE_edgeRep_mem_orbit (f ≫ g) ε)).choose
        • Γ''.edgeRep (edgeOrbitMap (f ≫ g) ε)
      = ((mem_orbit_iff.mp (onE_edgeRep_mem_orbit f ε)).choose *
          (mem_orbit_iff.mp (onE_edgeRep_mem_orbit g (edgeOrbitMap f ε))).choose)
        • Γ''.edgeRep (edgeOrbitMap (f ≫ g) ε) := by
    rw [hfg, mul_smul, hrep, hg, ← g.equivariant_E, hf]
    rfl
  have hstab := stabField_apply_eq_of_smul_eq key (x (edgeOrbitMap (f ≫ g) ε))
  have h : (mem_orbit_iff.mp (onE_edgeRep_mem_orbit (f ≫ g) ε)).choose
        (x (edgeOrbitMap (f ≫ g) ε) : L)
      = (mem_orbit_iff.mp (onE_edgeRep_mem_orbit f ε)).choose
          ((mem_orbit_iff.mp (onE_edgeRep_mem_orbit g (edgeOrbitMap f ε))).choose
            (y (edgeOrbitMap g (edgeOrbitMap f ε)) : L)) := by
    rw [hstab, AlgEquiv.mul_apply, hval]
  exact SetLike.coe_eq_coe.mp (e1.trans (h.trans e23.symm))

/-- Functoriality of `S(−)`, identity half (clause `RQ2-2.13-C1`).

Proof plan (G4): on the index component `orbitMap (𝟙 Γ) = id` holds by `Quotient.ind`; on the
algebra components both `stabFieldEquivOrbit` factors are the canonical translation by a group
element fixing the point, which `stabField_apply_eq_of_smul_eq` identifies with the identity.

@census none (clause witness for `RQ2-2.13-C1`)
-/
theorem speciesMap_id (Γ : RationalQuiver K L) :
    speciesMap (𝟙 Γ) = 𝟙 Γ.toSpecies := by
  refine EtaleSpecies.Hom.ext (funext (orbitMap_id_apply Γ)) ?_ ?_
  · exact Function.hfunext rfl fun i i' hii => by
      cases eq_of_heq hii; exact speciesMapOnL_heq_id Γ i
  · exact Function.hfunext rfl fun s s' hss => by
      cases eq_of_heq hss
      exact Function.hfunext rfl fun t t' htt => by
        cases eq_of_heq htt; exact speciesMapOnM_heq_id Γ s t

/-- Functoriality of `S(−)`, composition half (clause `RQ2-2.13-C1`); note the reversal, which is
what makes `S(−)` **contravariant**.

@census none (clause witness for `RQ2-2.13-C1`)
-/
theorem speciesMap_comp {Γ'' : RationalQuiver K L} (f : Γ ⟶ Γ') (g : Γ' ⟶ Γ'') :
    speciesMap (f ≫ g) = speciesMap g ≫ speciesMap f := by
  refine EtaleSpecies.Hom.ext (funext (orbitMap_comp_apply f g)) ?_ ?_
  · exact Function.hfunext rfl fun i i' hii => by
      cases eq_of_heq hii; exact speciesMapOnL_heq_comp f g i
  · exact Function.hfunext rfl fun s s' hss => by
      cases eq_of_heq hss
      exact Function.hfunext rfl fun t t' htt => by
        cases eq_of_heq htt; exact speciesMapOnM_heq_comp f g s t

end RationalQuiver

open CategoryTheory in
/-- **Clause `RQ2-2.13-C1`.** `S(−)` as a **contravariant** functor from `K`-rational quivers to
étale `K`-species, i.e. a functor into the opposite category.

@census none (clause witness for `RQ2-2.13-C1`)
-/
noncomputable def toSpeciesFunctor (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] : RationalQuiver K L ⥤ (EtaleSpecies.{u} K)ᵒᵖ where
  obj Γ := Opposite.op Γ.toSpecies
  map f := (RationalQuiver.speciesMap f).op
  map_id Γ := by rw [RationalQuiver.speciesMap_id]; rfl
  map_comp f g := by rw [RationalQuiver.speciesMap_comp]; rfl

/-! ## The functor `Γ_K(−)` on morphisms (clause `RQ2-2.13-C2`)

`Γ_K(−)` is defined on the étale `K`-species **split by `L`** — the §2.3 standing hypothesis
`RQ2-2.13-H1`, "`L` chosen large enough that all occurring finite étale algebras split over `L`" —
so its domain is the full subcategory `SplitSpecies K L`. It, too, is contravariant: a morphism
`g : X ⟶ Y` of species gives `Γ_K(g) : Γ_K(Y) ⟶ Γ_K(X)`, by **precomposition** — a vertex of
`Γ_K(Y)` is an embedding `τ : L̃_t → L`, and `τ ∘ ι_t` is a vertex of `Γ_K(X)`.

On edges the same recipe produces a `K`-algebra map `{}_{ι(s)}M_{ι(t)} → L`, and *its kernel* is the
maximal ideal `ε` of the target edge — which is why `kerMaximalSpectrum` below is needed: mathlib
has no lemma computing `Specm` of a finite product of fields, only the canonical decomposition
`IsArtinianRing.equivPi` (`ledger/MATHLIB-DECISIONS.tsv` `MD-S3-09` recorded exactly this gap).
-/

namespace EtaleSpecies

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]

/-- The kernel of a `K`-algebra map from a finite étale `K`-algebra to a field is a **maximal**
ideal, so it is a point of `Specm`. This is the step that sends an edge of `Γ_K(Y)` to an edge of
`Γ_K(X)`.

Proof plan (G4): `A ⧸ ker φ` embeds in the field `L`, so it is a domain; it is also a finite
`K`-algebra (a quotient of one), and a finite-dimensional domain over a field is a field; hence
`ker φ` is maximal (`Ideal.Quotient.maximal_of_isField`, `Module.Finite.of_surjective`).

@census none (helper for clause `RQ2-2.13-C2`)
-/
theorem isMaximal_ker {A : Type u} [CommRing A] [Algebra K A] [Module.Finite K A]
    (φ : A →ₐ[K] L) : (RingHom.ker φ).IsMaximal := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : IsDomain (A ⧸ RingHom.ker φ) :=
    Function.Injective.isDomain (RingHom.kerLift (φ : A →+* L))
      (RingHom.kerLift_injective (φ : A →+* L))
  exact Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)

/-- The point of `Specm A` cut out by a `K`-algebra map `A → L`. -/
noncomputable def kerMaximalSpectrum {A : Type u} [CommRing A] [Algebra K A] [Module.Finite K A]
    (φ : A →ₐ[K] L) : MaximalSpectrum A :=
  ⟨RingHom.ker φ, isMaximal_ker φ⟩

/-- A `K`-algebra map `{}_iM_j → L` factors through the **bundled** residue field at its own
kernel (`EtaleSpecies.residueField`, whose field and algebra instances are the bundle's — see
`ResidueFieldData`). The factorisation is `Ideal.Quotient.lift`; what needs saying is only that it
is a `K`-algebra map for the bundled structure, whose `algebraMap` is by construction the composite
`K → {}_iM_j → L_ε`. -/
noncomputable def kerResidueLift (S : EtaleSpecies.{u} K) {i j : S.I} (φ : S.M i j →ₐ[K] L) :
    S.residueField ⟨(i, j), kerMaximalSpectrum φ⟩ →ₐ[K] L where
  toFun := Ideal.Quotient.lift (RingHom.ker φ) (φ : S.M i j →+* L) fun _ ha => ha
  map_one' := map_one (Ideal.Quotient.lift (RingHom.ker φ) (φ : S.M i j →+* L) fun _ ha => ha)
  map_mul' := map_mul (Ideal.Quotient.lift (RingHom.ker φ) (φ : S.M i j →+* L) fun _ ha => ha)
  map_zero' := map_zero (Ideal.Quotient.lift (RingHom.ker φ) (φ : S.M i j →+* L) fun _ ha => ha)
  map_add' := map_add (Ideal.Quotient.lift (RingHom.ker φ) (φ : S.M i j →+* L) fun _ ha => ha)
  commutes' := fun r => φ.commutes r

/-- The étale `K`-species **split by `L`**, as an object property. -/
def splitBy (K L : Type u) [Field K] [Field L] [Algebra K L] :
    CategoryTheory.ObjectProperty (EtaleSpecies.{u} K) := fun S => S.IsSplitBy L

/-- **Clause `RQ2-2.13-C2`, vertices.** A vertex of `Γ_K(T)` is an embedding `τ : L̃_t → L`;
precomposing with `ι_t : L_{ι(t)} → L̃_t` gives a vertex of `Γ_K(S)`. -/
def vertexMap {S T : EtaleSpecies.{u} K} (g : S ⟶ T) (L : Type u) [Field L] [Algebra K L] :
    T.vertexSet L → S.vertexSet L :=
  fun v => ⟨g.onI v.1, v.2.comp (g.onL v.1)⟩

/-- **Clause `RQ2-2.13-C2`, edges.** An edge of `Γ_K(T)` is an embedding `τ : L̃_ε → L`; composing
`{}_{ι(s)}M_{ι(t)} → {}_sM̃_t → L̃_ε → L` gives a `K`-algebra map to `L`, whose kernel is the
maximal ideal of the resulting edge of `Γ_K(S)` and through whose residue field it factors. -/
noncomputable def edgeMap {S T : EtaleSpecies.{u} K} (g : S ⟶ T) (L : Type u) [Field L]
    [Algebra K L] : T.edgeSet L → S.edgeSet L := fun e =>
  ⟨⟨(g.onI e.1.1.1, g.onI e.1.1.2),
      kerMaximalSpectrum (e.2.comp ((T.residueMap e.1).comp (g.onM e.1.1.1 e.1.1.2)))⟩,
    S.kerResidueLift (e.2.comp ((T.residueMap e.1).comp (g.onM e.1.1.1 e.1.1.2)))⟩


/-! ### Kernels, and the edge-transport tool for `Γ_K(−)`

`Γ_K(g)`'s edge component is indexed by a *kernel*, so every edge identity below is an identity of
maximal ideals plus an identity of the induced maps on the residue field. `edgeSet_ext_of_val` is
the `vertexSet_ext_of_val` of the edge side: it takes the index equality and a comparison **on
elements of `{}_iM_j`**, and hands back the equation in `E`.
-/

/-- The kernel of the residue map is its own maximal ideal.

@census none (helper for clause `RQ2-2.13-C2`)
-/
theorem ker_residueMap (S : EtaleSpecies.{u} K) (c : S.edgeIndexSet) :
    RingHom.ker (S.residueMap c) = c.2.asIdeal := by
  ext x
  simp only [RingHom.mem_ker]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Postcomposing the residue map with **any** `K`-algebra map to a field does not change the
kernel: a ring map out of a field is injective. This is what identifies `Γ_K(𝟙)` with `𝟙`.

@census none (helper for clause `RQ2-2.13-C2`)
-/
theorem ker_comp_residueMap (S : EtaleSpecies.{u} K) (c : S.edgeIndexSet)
    (τ : S.residueField c →ₐ[K] L) :
    RingHom.ker (τ.comp (S.residueMap c)) = c.2.asIdeal := by
  have hinj : Function.Injective τ := (τ : S.residueField c →+* L).injective
  ext x
  simp only [RingHom.mem_ker]
  exact Iff.trans (map_eq_zero_iff _ hinj) Ideal.Quotient.eq_zero_iff_mem

/-- Twisting a `K`-algebra map to `L` by a Galois element does not change its kernel. This is the
whole content of the edge half of `Γ_K(g)`'s equivariance.

@census none (helper for clause `RQ2-2.13-C2`)
-/
theorem ker_smul_comp {A : Type u} [CommRing A] [Algebra K A] (φ : A →ₐ[K] L) (σ : Gal(L/K)) :
    RingHom.ker (σ • φ : A →ₐ[K] L) = RingHom.ker φ := by
  ext y
  simp only [RingHom.mem_ker]
  show σ (φ y) = 0 ↔ φ y = 0
  exact map_eq_zero_iff _ (σ : L ≃ₐ[K] L).injective

/-- **The transport tool for the edge side.** Two edges of `Γ_K(S)` over the same pair of indices
are equal as soon as their maximal ideals agree and the two embeddings agree *after the residue
map*, i.e. on elements of `{}_iM_j`. As with `vertexSet_ext_of_val`, the `Sigma` transport is
confined to this one `cases`.

@census none (helper for clauses `RQ2-2.13-C2`, `C3`)
-/
theorem edgeSet_ext_of_val {S : EtaleSpecies.{u} K} {p : S.I × S.I}
    {m₁ m₂ : MaximalSpectrum (S.M p.1 p.2)} (h : m₁ = m₂)
    {φ : S.residueField ⟨p, m₁⟩ →ₐ[K] L} {ψ : S.residueField ⟨p, m₂⟩ →ₐ[K] L}
    (h2 : ∀ x : S.M p.1 p.2, φ (S.residueMap ⟨p, m₁⟩ x) = ψ (S.residueMap ⟨p, m₂⟩ x)) :
    (⟨⟨p, m₁⟩, φ⟩ : S.edgeSet L) = ⟨⟨p, m₂⟩, ψ⟩ := by
  cases h
  refine congrArg (Sigma.mk _) (AlgHom.ext fun y => ?_)
  obtain ⟨x, rfl⟩ := S.residueMap_surjective _ y
  exact h2 x

/-- **The transport tool in the form the summit uses it.** An edge of `Γ_K(S)` presented as
"the kernel of `φ₁`, with the map `φ₁` induces on the residue field" equals *any* edge `⟨⟨p₂,m₂⟩,ψ⟩`
as soon as the index pairs agree and `φ₁` agrees with `ψ ∘ (residue map)` on `HEq`-related
elements. The maximal ideal is then forced: it is `ker (ψ ∘ residueMap) = m₂`
(`ker_comp_residueMap`), so the caller never has to produce it.

@census none (helper for clauses `RQ2-2.13-C2`, `C3`)
-/
theorem edgeSet_ext_of_emb {S : EtaleSpecies.{u} K} {p₁ p₂ : S.I × S.I} (hp : p₁ = p₂)
    [Module.Finite K (S.M p₁.1 p₁.2)] {φ₁ : S.M p₁.1 p₁.2 →ₐ[K] L}
    {m₂ : MaximalSpectrum (S.M p₂.1 p₂.2)} {ψ : S.residueField ⟨p₂, m₂⟩ →ₐ[K] L}
    (h : ∀ (x : S.M p₁.1 p₁.2) (y : S.M p₂.1 p₂.2), HEq x y →
      φ₁ x = ψ (S.residueMap ⟨p₂, m₂⟩ y)) :
    (⟨⟨p₁, kerMaximalSpectrum φ₁⟩, S.kerResidueLift φ₁⟩ : S.edgeSet L) = ⟨⟨p₂, m₂⟩, ψ⟩ := by
  cases hp
  have hcomp : φ₁ = ψ.comp (S.residueMap ⟨p₁, m₂⟩) := AlgHom.ext fun x => h x x HEq.rfl
  subst hcomp
  exact edgeSet_ext_of_val (MaximalSpectrum.ext (ker_comp_residueMap S ⟨p₁, m₂⟩ ψ))
    (fun _ => rfl)

/-- The converse reading of `edgeSet_ext_of_val`: an equation between two edges of `Γ_K(S)` gives,
after the index transport, an equation between the two embeddings **on elements of `{}_iM_j`**.
This is what turns `Φ_E(e) = Φ_E(f)` into a usable statement.

@census none (helper for clause `RQ2-2.13-C4`)
-/
theorem edgeSet_val_of_eq {S : EtaleSpecies.{u} K} {c₁ c₂ : S.edgeIndexSet}
    {φ : S.residueField c₁ →ₐ[K] L} {ψ : S.residueField c₂ →ₐ[K] L}
    (h : (⟨c₁, φ⟩ : S.edgeSet L) = ⟨c₂, ψ⟩)
    {x : S.M c₁.1.1 c₁.1.2} {y : S.M c₂.1.1 c₂.1.2} (hxy : HEq x y) :
    φ (S.residueMap c₁ x) = ψ (S.residueMap c₂ y) := by
  rw [Sigma.mk.injEq] at h
  obtain ⟨hc, hφ⟩ := h
  cases hc
  cases hφ
  cases hxy
  rfl

/-! ### The vertex fields of `Γ_K(S)` (clause `RQ2-2.13-C4`, the counit's vertex component)

`L(v)` for a vertex `v = (i, τ)` of `Γ_K(S)` is the **image** of `τ`: the stabilizer of `(i,τ)` is
by definition the subgroup fixing `im τ` pointwise, and the Galois correspondence
(`IsGalois.fixedField_fixingSubgroup`) turns that into `L^{G_v} = im τ`. Since `τ` is injective this
identifies `L_i` with `L(v)` — which is exactly the algebra component of `S → S(Γ_K(S))`.
-/

open MulAction in
theorem smul_vertexSet_eq_iff (S : EtaleSpecies.{u} K) (σ : Gal(L/K)) (v : S.vertexSet L) :
    σ • v = v ↔ ∀ a : S.L v.1, σ (v.2 a) = v.2 a := by
  constructor
  · intro h a
    have h2 : HEq (σ • v.2) v.2 := by
      have h' : (⟨v.1, σ • v.2⟩ : S.vertexSet L) = ⟨v.1, v.2⟩ := h
      rw [Sigma.mk.injEq] at h'
      exact h'.2
    exact congrArg (fun f : S.L v.1 →ₐ[K] L => f a) (eq_of_heq h2)
  · intro h
    show (⟨v.1, σ • v.2⟩ : S.vertexSet L) = v
    exact congrArg (Sigma.mk v.1) (AlgHom.ext h)

open MulAction in
theorem stabField_vertexSet [IsGalois K L] [FiniteDimensional K L]
    (S : EtaleSpecies.{u} K) (v : S.vertexSet L) :
    stabField K L v = (v.2).fieldRange := by
  have hstab : stabilizer Gal(L/K) v = ((v.2).fieldRange : IntermediateField K L).fixingSubgroup := by
    ext σ
    rw [mem_stabilizer_iff, S.smul_vertexSet_eq_iff σ v, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h y hy
      obtain ⟨a, rfl⟩ := (AlgHom.mem_fieldRange).mp hy
      exact h a
    · intro h a
      exact h (v.2 a) (AlgHom.mem_fieldRange.mpr ⟨a, rfl⟩)
  rw [stabField, hstab]
  exact IsGalois.fixedField_fixingSubgroup _

/-! The same for edges: `L(e)` for an edge `e = (ε, τ)` of `Γ_K(S)` is the image of `τ`, so `L_ε`
is identified with `L(e)`. This is the algebra component of the counit on the edge side. -/

open MulAction in
theorem smul_edgeSet_eq_iff (S : EtaleSpecies.{u} K) (σ : Gal(L/K)) (e : S.edgeSet L) :
    σ • e = e ↔ ∀ a : S.residueField e.1, σ (e.2 a) = e.2 a := by
  constructor
  · intro h a
    have h2 : HEq (σ • e.2) e.2 := by
      have h' : (⟨e.1, σ • e.2⟩ : S.edgeSet L) = ⟨e.1, e.2⟩ := h
      rw [Sigma.mk.injEq] at h'
      exact h'.2
    exact congrArg (fun f : S.residueField e.1 →ₐ[K] L => f a) (eq_of_heq h2)
  · intro h
    show (⟨e.1, σ • e.2⟩ : S.edgeSet L) = e
    exact congrArg (Sigma.mk e.1) (AlgHom.ext h)

open MulAction in
theorem stabField_edgeSet [IsGalois K L] [FiniteDimensional K L]
    (S : EtaleSpecies.{u} K) (e : S.edgeSet L) :
    stabField K L e = (e.2).fieldRange := by
  have hstab : stabilizer Gal(L/K) e = ((e.2).fieldRange : IntermediateField K L).fixingSubgroup := by
    ext σ
    rw [mem_stabilizer_iff, S.smul_edgeSet_eq_iff σ e, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h y hy
      obtain ⟨a, rfl⟩ := (AlgHom.mem_fieldRange).mp hy
      exact h a
    · intro h a
      exact h (e.2 a) (AlgHom.mem_fieldRange.mpr ⟨a, rfl⟩)
  rw [stabField, hstab]
  exact IsGalois.fixedField_fixingSubgroup _

/-- The maximal ideal of an edge index whose vertex pair is known to be `p`, extracted without a
`cast`: `c` is destructured first, so the index equality is an equation between variables and one
`cases` does the transport. -/
def edgeIndexOfMem {S : EtaleSpecies.{u} K} {p : S.I × S.I} :
    ∀ {c : S.edgeIndexSet}, c.1 = p → MaximalSpectrum (S.M p.1 p.2)
  | ⟨_, m⟩, h => by cases h; exact m

@[simp] theorem edgeIndex_mk_edgeIndexOfMem {S : EtaleSpecies.{u} K} {p : S.I × S.I}
    : ∀ {c : S.edgeIndexSet} (h : c.1 = p),
      (⟨p, edgeIndexOfMem h⟩ : S.edgeIndexSet) = c
  | ⟨_, _⟩, h => by cases h; rfl

/-! ### Reconciling the bundled residue field with the ambient quotient (finding **C-7**)

The G2 verification flagged that `prod_decomposition` produces the quotient rings `{}_iM_j/ε` with
mathlib's `Ideal.Quotient` structure, whereas `residueField` carries the *bundle's* structure
(§8.2's option (b)), and asked how the two are reconciled. **Measured answer: they agree on the
nose.** The bundle's `Algebra K` is `RingHom.toAlgebra ((Ideal.Quotient.mk ε).comp (algebraMap K _))`
and mathlib's is the same composite, and the bundle's `Field` is `Ideal.Quotient.field` built on the
same `CommRing`; so the identity map is an `AlgEquiv` and `residueFieldEquivQuotient` is proved by
`rfl` in every field. No `Algebra.algebra_ext` is needed, and finding C-7 costs nothing.

The canonical decomposition is also recorded here as a **def** rather than as the `Nonempty` of
`prod_decomposition`: the counit's compatibility squares need to know that the `ε`-component of `x`
is `x mod ε`, which `Nonempty.some` would discard.
-/

noncomputable def residueFieldEquivQuotient (S : EtaleSpecies.{u} K) (c : S.edgeIndexSet) :
    S.residueField c ≃ₐ[K] (S.M c.1.1 c.1.2 ⧸ c.2.asIdeal) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl
  map_add' := fun _ _ => rfl
  commutes' := fun _ => rfl

noncomputable def prodDecompositionEquiv (S : EtaleSpecies.{u} K) (i j : S.I) :
    S.M i j ≃ₐ[K] ∀ m : MaximalSpectrum (S.M i j), S.M i j ⧸ m.asIdeal :=
  letI : IsArtinianRing (S.M i j) := IsArtinianRing.of_finite K (S.M i j)
  letI : IsReduced (S.M i j) := Algebra.FormallyUnramified.isReduced_of_field K (S.M i j)
  (IsArtinianRing.equivPi (S.M i j)).restrictScalars K

theorem prodDecompositionEquiv_apply (S : EtaleSpecies.{u} K) (i j : S.I) (x : S.M i j)
    (m : MaximalSpectrum (S.M i j)) :
    S.prodDecompositionEquiv i j x m = Ideal.Quotient.mk m.asIdeal x := rfl

noncomputable def residueFieldEquivOfEq {S : EtaleSpecies.{u} K} {c c' : S.edgeIndexSet}
    (h : c = c') : S.residueField c ≃ₐ[K] S.residueField c' := by
  cases h; exact AlgEquiv.refl

/-! The two structure-map transports the counit's compatibility squares run on: carrying the source
(resp. target) vertex of an edge along an equality of indices. Both are `cases h; rfl`. -/

theorem edgeSource_congr {S : EtaleSpecies.{u} K} {c c' : S.edgeIndexSet} (h : c = c')
    (τ : S.residueField c' →ₐ[K] L) :
    (⟨c.1.1, (τ.comp (residueFieldEquivOfEq h).toAlgHom).comp (S.structLeft c)⟩
        : S.vertexSet L)
      = ⟨c'.1.1, τ.comp (S.structLeft c')⟩ := by
  cases h; rfl

theorem edgeTarget_congr {S : EtaleSpecies.{u} K} {c c' : S.edgeIndexSet} (h : c = c')
    (τ : S.residueField c' →ₐ[K] L) :
    (⟨c.1.2, (τ.comp (residueFieldEquivOfEq h).toAlgHom).comp (S.structRight c)⟩
        : S.vertexSet L)
      = ⟨c'.1.2, τ.comp (S.structRight c')⟩ := by
  cases h; rfl

theorem sigma_snd_eq {ι : Type u} {A : ι → Type u} {i : ι} {a b : A i}
    (h : (⟨i, a⟩ : Σ i, A i) = ⟨i, b⟩) : a = b := by
  rw [Sigma.mk.injEq] at h
  exact eq_of_heq h.2



/-! ### Family-indexed `HEq` tools

The counit's naturality compares algebra maps whose *domains* are indexed by two propositionally
equal indices. As always the transport is paid once, in lemmas whose index equality is between
variables. -/

theorem heq_algHom_fam {ι : Type u} {A : ι → Type u} [∀ i, CommRing (A i)]
    [∀ i, Algebra K (A i)] {B : Type u} [CommRing B] [Algebra K B] {i i' : ι} (h : i = i')
    {φ : A i →ₐ[K] B} {ψ : A i' →ₐ[K] B}
    (hval : ∀ (a : A i) (a' : A i'), HEq a a' → φ a = ψ a') : HEq φ ψ := by
  cases h
  exact heq_of_eq (AlgHom.ext fun a => hval a a HEq.rfl)

theorem sigma_heq_snd {ι : Type u} {A : ι → Type u} {i i' : ι} {a : A i} {a' : A i'}
    (h : (⟨i, a⟩ : Σ i, A i) = ⟨i', a'⟩) : HEq a a' := by
  rw [Sigma.mk.injEq] at h
  exact h.2

theorem heq_algHom_apply_fam {ι : Type u} {A : ι → Type u} [∀ i, CommRing (A i)]
    [∀ i, Algebra K (A i)] {B : Type u} [CommRing B] [Algebra K B] {i i' : ι} (h : i = i')
    {φ : A i →ₐ[K] B} {ψ : A i' →ₐ[K] B} (hφ : HEq φ ψ) {a : A i} {a' : A i'} (ha : HEq a a') :
    φ a = ψ a' := by
  cases h; cases hφ; cases ha; rfl


/-! ### A componentwise-bijective morphism of species is an isomorphism

`RQ2-2.13-C4` asks for an *isomorphism* `S ≅ S(Γ_K(S))`, and the previous sections produce a morphism
whose three components are bijections. Turning one into the other is the species analogue of
`RationalQuiver.isIso_of_bijective`, and it is harder for the same reason `EtaleSpecies.Hom`
equality is harder: inverting the index component forces a transport in the algebra components (the
equation `ι(ι⁻¹ i) = i` is only propositional), and the two round trips are `Hom` equalities, hence
`HEq` goals.

Both are handled by the §12 discipline. `famTransport` is the generic index transport — stated for
an arbitrary family so that one definition serves `L`, `M` and both species — and every fact about
it (`famTransport_heq_id`, `famTransport_left`/`_right`, `onL_famTransport`, `onM_famTransport`) is
`cases h; rfl`. The consumers then never see a `▸`.

One elaboration note: the `M`-transports must have their index **pair** pinned by an explicit
`show ... = (u, v) from ...`, because unifying `(fun p => S.M p.1 p.2) ?p` with `S.M u v` is a
higher-order problem Lean will not solve on its own.
-/

section HomInv

variable {S T : EtaleSpecies.{u} K}

noncomputable def famTransport {ι : Type u} (A : ι → Type u) [∀ i, CommRing (A i)]
    [∀ i, Algebra K (A i)] {i i' : ι} (h : i = i') : A i ≃ₐ[K] A i' := by
  cases h; exact AlgEquiv.refl

theorem famTransport_heq_id {ι : Type u} (A : ι → Type u) [∀ i, CommRing (A i)]
    [∀ i, Algebra K (A i)] {i i' : ι} (h : i = i') :
    HEq (famTransport (K := K) A h).toAlgHom (AlgHom.id K (A i')) := by
  cases h; rfl

theorem famTransport_left {S : EtaleSpecies.{u} K} {u u' v v' : S.I} (hu : u = u') (hv : v = v') :
    ((famTransport (K := K) (fun p : S.I × S.I => S.M p.1 p.2)
        (Prod.ext hu hv : (u, v) = (u', v'))).toAlgHom).comp (S.left u v)
      = (S.left u' v').comp (famTransport (K := K) S.L hu).toAlgHom := by
  cases hu; cases hv; rfl

theorem famTransport_right {S : EtaleSpecies.{u} K} {u u' v v' : S.I} (hu : u = u') (hv : v = v') :
    ((famTransport (K := K) (fun p : S.I × S.I => S.M p.1 p.2)
        (Prod.ext hu hv : (u, v) = (u', v'))).toAlgHom).comp (S.right u v)
      = (S.right u' v').comp (famTransport (K := K) S.L hv).toAlgHom := by
  cases hu; cases hv; rfl


variable {S T : EtaleSpecies.{u} K}

/-- The index component of the inverse of a componentwise-bijective morphism. -/
noncomputable def homInvOnI (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f)) :
    S.I → T.I := (Equiv.ofBijective _ hI).symm

theorem homInvOnI_spec (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f)) (i : S.I) :
    EtaleSpecies.Hom.onI f (homInvOnI f hI i) = i := (Equiv.ofBijective _ hI).apply_symm_apply i

/-- The vertex-algebra component of the inverse. -/
noncomputable def homInvOnL (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f))
    (hL : ∀ t, Function.Bijective (EtaleSpecies.Hom.onL f t)) (i : S.I) :
    T.L (homInvOnI f hI i) →ₐ[K] S.L i :=
  (famTransport (K := K) S.L (homInvOnI_spec f hI i)).toAlgHom.comp
    (AlgEquiv.ofBijective (EtaleSpecies.Hom.onL f (homInvOnI f hI i)) (hL _)).symm.toAlgHom

theorem homInvOnL_apply (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f))
    (hL : ∀ t, Function.Bijective (EtaleSpecies.Hom.onL f t)) (i : S.I)
    (x : S.L (EtaleSpecies.Hom.onI f (homInvOnI f hI i))) :
    homInvOnL f hI hL i (EtaleSpecies.Hom.onL f (homInvOnI f hI i) x)
      = famTransport (K := K) S.L (homInvOnI_spec f hI i) x :=
  congrArg (famTransport (K := K) S.L (homInvOnI_spec f hI i))
    ((AlgEquiv.ofBijective (EtaleSpecies.Hom.onL f (homInvOnI f hI i)) (hL _)).symm_apply_apply x)

/-- The edge-algebra component of the inverse. -/
noncomputable def homInvOnM (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f))
    (hM : ∀ s t, Function.Bijective (EtaleSpecies.Hom.onM f s t)) (u v : S.I) :
    T.M (homInvOnI f hI u) (homInvOnI f hI v) →ₐ[K] S.M u v :=
  (famTransport (K := K) (fun p : S.I × S.I => S.M p.1 p.2)
      (show ((EtaleSpecies.Hom.onI f (homInvOnI f hI u),
          EtaleSpecies.Hom.onI f (homInvOnI f hI v)) : S.I × S.I) = (u, v) from
        Prod.ext (homInvOnI_spec f hI u) (homInvOnI_spec f hI v))).toAlgHom.comp
    (AlgEquiv.ofBijective (EtaleSpecies.Hom.onM f (homInvOnI f hI u) (homInvOnI f hI v))
      (hM _ _)).symm.toAlgHom

theorem homInvOnM_apply (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f))
    (hM : ∀ s t, Function.Bijective (EtaleSpecies.Hom.onM f s t)) (u v : S.I)
    (x : S.M (EtaleSpecies.Hom.onI f (homInvOnI f hI u))
      (EtaleSpecies.Hom.onI f (homInvOnI f hI v))) :
    homInvOnM f hI hM u v
        (EtaleSpecies.Hom.onM f (homInvOnI f hI u) (homInvOnI f hI v) x)
      = famTransport (K := K) (fun p : S.I × S.I => S.M p.1 p.2)
          (show ((EtaleSpecies.Hom.onI f (homInvOnI f hI u),
          EtaleSpecies.Hom.onI f (homInvOnI f hI v)) : S.I × S.I) = (u, v) from
        Prod.ext (homInvOnI_spec f hI u) (homInvOnI_spec f hI v)) x :=
  congrArg (famTransport (K := K) (fun p : S.I × S.I => S.M p.1 p.2)
      (show ((EtaleSpecies.Hom.onI f (homInvOnI f hI u),
          EtaleSpecies.Hom.onI f (homInvOnI f hI v)) : S.I × S.I) = (u, v) from
        Prod.ext (homInvOnI_spec f hI u) (homInvOnI_spec f hI v)))
    ((AlgEquiv.ofBijective (EtaleSpecies.Hom.onM f (homInvOnI f hI u) (homInvOnI f hI v))
      (hM _ _)).symm_apply_apply x)

noncomputable def homInv (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f))
    (hL : ∀ t, Function.Bijective (EtaleSpecies.Hom.onL f t))
    (hM : ∀ s t, Function.Bijective (EtaleSpecies.Hom.onM f s t)) : T ⟶ S where
  onI := homInvOnI f hI
  onL := homInvOnL f hI hL
  onM := homInvOnM f hI hM
  compat_left := by
    intro u v
    refine AlgHom.ext fun y => ?_
    obtain ⟨x, rfl⟩ := (hL (homInvOnI f hI u)).2 y
    have hsq : T.left (homInvOnI f hI u) (homInvOnI f hI v)
          (EtaleSpecies.Hom.onL f (homInvOnI f hI u) x)
        = EtaleSpecies.Hom.onM f (homInvOnI f hI u) (homInvOnI f hI v) (S.left _ _ x) :=
      (congrArg (fun g => g x)
        (f.compat_left (homInvOnI f hI u) (homInvOnI f hI v))).symm
    show homInvOnM f hI hM u v (T.left _ _ (EtaleSpecies.Hom.onL f _ x))
      = S.left u v (homInvOnL f hI hL u (EtaleSpecies.Hom.onL f _ x))
    rw [hsq, homInvOnM_apply, homInvOnL_apply]
    exact congrArg (fun g => g x)
      (famTransport_left (homInvOnI_spec f hI u) (homInvOnI_spec f hI v))
  compat_right := by
    intro u v
    refine AlgHom.ext fun y => ?_
    obtain ⟨x, rfl⟩ := (hL (homInvOnI f hI v)).2 y
    have hsq : T.right (homInvOnI f hI u) (homInvOnI f hI v)
          (EtaleSpecies.Hom.onL f (homInvOnI f hI v) x)
        = EtaleSpecies.Hom.onM f (homInvOnI f hI u) (homInvOnI f hI v) (S.right _ _ x) :=
      (congrArg (fun g => g x)
        (f.compat_right (homInvOnI f hI u) (homInvOnI f hI v))).symm
    show homInvOnM f hI hM u v (T.right _ _ (EtaleSpecies.Hom.onL f _ x))
      = S.right u v (homInvOnL f hI hL v (EtaleSpecies.Hom.onL f _ x))
    rw [hsq, homInvOnM_apply, homInvOnL_apply]
    exact congrArg (fun g => g x)
      (famTransport_right (homInvOnI_spec f hI u) (homInvOnI_spec f hI v))


theorem onL_famTransport (f : S ⟶ T) {t t' : T.I} (h : t = t') :
    (famTransport (K := K) T.L h).toAlgHom.comp (EtaleSpecies.Hom.onL f t)
      = (EtaleSpecies.Hom.onL f t').comp
          (famTransport (K := K) S.L (congrArg (EtaleSpecies.Hom.onI f) h)).toAlgHom := by
  cases h; rfl

theorem homInv_comp_onL (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f))
    (hL : ∀ t, Function.Bijective (EtaleSpecies.Hom.onL f t)) (i : S.I) :
    (homInvOnL f hI hL i).comp (EtaleSpecies.Hom.onL f (homInvOnI f hI i))
      = (famTransport (K := K) S.L (homInvOnI_spec f hI i)).toAlgHom :=
  AlgHom.ext fun x => homInvOnL_apply f hI hL i x

theorem heq_homInv_comp_onL (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f))
    (hL : ∀ t, Function.Bijective (EtaleSpecies.Hom.onL f t)) (i : S.I) :
    HEq ((homInvOnL f hI hL i).comp (EtaleSpecies.Hom.onL f (homInvOnI f hI i)))
      (AlgHom.id K (S.L i)) := by
  rw [homInv_comp_onL]
  exact famTransport_heq_id S.L (homInvOnI_spec f hI i)

theorem homInv_comp_onM (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f))
    (hM : ∀ s t, Function.Bijective (EtaleSpecies.Hom.onM f s t)) (u v : S.I) :
    (homInvOnM f hI hM u v).comp
        (EtaleSpecies.Hom.onM f (homInvOnI f hI u) (homInvOnI f hI v))
      = (famTransport (K := K) (fun p : S.I × S.I => S.M p.1 p.2)
          (show ((EtaleSpecies.Hom.onI f (homInvOnI f hI u),
              EtaleSpecies.Hom.onI f (homInvOnI f hI v)) : S.I × S.I) = (u, v) from
            Prod.ext (homInvOnI_spec f hI u) (homInvOnI_spec f hI v))).toAlgHom :=
  AlgHom.ext fun x => homInvOnM_apply f hI hM u v x

theorem heq_homInv_comp_onM (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f))
    (hM : ∀ s t, Function.Bijective (EtaleSpecies.Hom.onM f s t)) (u v : S.I) :
    HEq ((homInvOnM f hI hM u v).comp
        (EtaleSpecies.Hom.onM f (homInvOnI f hI u) (homInvOnI f hI v)))
      (AlgHom.id K (S.M u v)) := by
  rw [homInv_comp_onM]
  exact famTransport_heq_id (fun p : S.I × S.I => S.M p.1 p.2) _

theorem homInv_hom_id (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f))
    (hL : ∀ t, Function.Bijective (EtaleSpecies.Hom.onL f t))
    (hM : ∀ s t, Function.Bijective (EtaleSpecies.Hom.onM f s t)) :
    f ≫ homInv f hI hL hM = 𝟙 S := by
  refine EtaleSpecies.Hom.ext (funext (homInvOnI_spec f hI)) ?_ ?_
  · exact Function.hfunext rfl fun i i' hii => by
      cases eq_of_heq hii; exact heq_homInv_comp_onL f hI hL i
  · exact Function.hfunext rfl fun u u' huu => by
      cases eq_of_heq huu
      exact Function.hfunext rfl fun v v' hvv => by
        cases eq_of_heq hvv; exact heq_homInv_comp_onM f hI hM u v


theorem homInvOnI_left (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f)) (t : T.I) :
    homInvOnI f hI (EtaleSpecies.Hom.onI f t) = t :=
  (Equiv.ofBijective _ hI).symm_apply_apply t

theorem onM_famTransport (f : S ⟶ T) {u u' v v' : T.I} (hu : u = u') (hv : v = v') :
    (famTransport (K := K) (fun p : T.I × T.I => T.M p.1 p.2)
        (show ((u, v) : T.I × T.I) = (u', v') from Prod.ext hu hv)).toAlgHom.comp
        (EtaleSpecies.Hom.onM f u v)
      = (EtaleSpecies.Hom.onM f u' v').comp
          (famTransport (K := K) (fun p : S.I × S.I => S.M p.1 p.2)
            (show ((EtaleSpecies.Hom.onI f u, EtaleSpecies.Hom.onI f v) : S.I × S.I)
                = (EtaleSpecies.Hom.onI f u', EtaleSpecies.Hom.onI f v') from
              Prod.ext (congrArg (EtaleSpecies.Hom.onI f) hu)
                (congrArg (EtaleSpecies.Hom.onI f) hv))).toAlgHom := by
  cases hu; cases hv; rfl

theorem comp_homInv_onL (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f))
    (hL : ∀ t, Function.Bijective (EtaleSpecies.Hom.onL f t)) (t : T.I) :
    (EtaleSpecies.Hom.onL f t).comp (homInvOnL f hI hL (EtaleSpecies.Hom.onI f t))
      = (famTransport (K := K) T.L (homInvOnI_left f hI t)).toAlgHom := by
  refine AlgHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (hL (homInvOnI f hI (EtaleSpecies.Hom.onI f t))).2 y
  show EtaleSpecies.Hom.onL f t
      (homInvOnL f hI hL (EtaleSpecies.Hom.onI f t) (EtaleSpecies.Hom.onL f _ x))
    = famTransport (K := K) T.L (homInvOnI_left f hI t) (EtaleSpecies.Hom.onL f _ x)
  rw [homInvOnL_apply]
  exact (congrArg (fun g => g x) (onL_famTransport f (homInvOnI_left f hI t))).symm

theorem comp_homInv_onM (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f))
    (hM : ∀ s t, Function.Bijective (EtaleSpecies.Hom.onM f s t)) (u v : T.I) :
    (EtaleSpecies.Hom.onM f u v).comp
        (homInvOnM f hI hM (EtaleSpecies.Hom.onI f u) (EtaleSpecies.Hom.onI f v))
      = (famTransport (K := K) (fun p : T.I × T.I => T.M p.1 p.2)
          (show ((homInvOnI f hI (EtaleSpecies.Hom.onI f u),
              homInvOnI f hI (EtaleSpecies.Hom.onI f v)) : T.I × T.I) = (u, v) from
            Prod.ext (homInvOnI_left f hI u) (homInvOnI_left f hI v))).toAlgHom := by
  refine AlgHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (hM (homInvOnI f hI (EtaleSpecies.Hom.onI f u))
    (homInvOnI f hI (EtaleSpecies.Hom.onI f v))).2 y
  show EtaleSpecies.Hom.onM f u v
      (homInvOnM f hI hM (EtaleSpecies.Hom.onI f u) (EtaleSpecies.Hom.onI f v)
        (EtaleSpecies.Hom.onM f _ _ x))
    = famTransport (K := K) (fun p : T.I × T.I => T.M p.1 p.2)
        (show ((homInvOnI f hI (EtaleSpecies.Hom.onI f u),
            homInvOnI f hI (EtaleSpecies.Hom.onI f v)) : T.I × T.I) = (u, v) from
          Prod.ext (homInvOnI_left f hI u) (homInvOnI_left f hI v))
        (EtaleSpecies.Hom.onM f _ _ x)
  rw [homInvOnM_apply]
  exact (congrArg (fun g => g x)
    (onM_famTransport f (homInvOnI_left f hI u) (homInvOnI_left f hI v))).symm

theorem homInv_inv_id (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f))
    (hL : ∀ t, Function.Bijective (EtaleSpecies.Hom.onL f t))
    (hM : ∀ s t, Function.Bijective (EtaleSpecies.Hom.onM f s t)) :
    homInv f hI hL hM ≫ f = 𝟙 T := by
  refine EtaleSpecies.Hom.ext (funext (homInvOnI_left f hI)) ?_ ?_
  · refine Function.hfunext rfl fun t t' htt => ?_
    cases eq_of_heq htt
    show HEq ((EtaleSpecies.Hom.onL f t).comp
      (homInvOnL f hI hL (EtaleSpecies.Hom.onI f t))) (AlgHom.id K (T.L t))
    rw [comp_homInv_onL]
    exact famTransport_heq_id T.L (homInvOnI_left f hI t)
  · refine Function.hfunext rfl fun u u' huu => ?_
    cases eq_of_heq huu
    refine Function.hfunext rfl fun v v' hvv => ?_
    cases eq_of_heq hvv
    show HEq ((EtaleSpecies.Hom.onM f u v).comp
      (homInvOnM f hI hM (EtaleSpecies.Hom.onI f u) (EtaleSpecies.Hom.onI f v)))
      (AlgHom.id K (T.M u v))
    rw [comp_homInv_onM]
    exact famTransport_heq_id (fun p : T.I × T.I => T.M p.1 p.2) _

theorem isIso_of_bijective (f : S ⟶ T) (hI : Function.Bijective (EtaleSpecies.Hom.onI f))
    (hL : ∀ t, Function.Bijective (EtaleSpecies.Hom.onL f t))
    (hM : ∀ s t, Function.Bijective (EtaleSpecies.Hom.onM f s t)) : IsIso f :=
  ⟨homInv f hI hL hM, homInv_hom_id f hI hL hM, homInv_inv_id f hI hL hM⟩


/-! ### Congruence lemmas for the counit's edge naturality

All of them are `cases h; rfl`; they exist so that the one long chain of §21 never writes a `▸`. -/

theorem heq_residueFieldEquivOfEq {S : EtaleSpecies.{u} K} {c c' : S.edgeIndexSet} (h : c = c')
    (x : S.residueField c) : HEq (residueFieldEquivOfEq h x) x := by
  cases h; rfl

theorem heq_residueMap {S : EtaleSpecies.{u} K} {c c' : S.edgeIndexSet} (h : c = c')
    {w : S.M c.1.1 c.1.2} {w' : S.M c'.1.1 c'.1.2} (hw : HEq w w') :
    HEq (S.residueMap c w) (S.residueMap c' w') := by
  cases h; cases hw; rfl

theorem heq_onM_apply {S T : EtaleSpecies.{u} K} (g : S ⟶ T) {p p' : T.I × T.I} (h : p = p')
    {w : S.M (EtaleSpecies.Hom.onI g p.1) (EtaleSpecies.Hom.onI g p.2)}
    {w' : S.M (EtaleSpecies.Hom.onI g p'.1) (EtaleSpecies.Hom.onI g p'.2)} (hw : HEq w w') :
    HEq (EtaleSpecies.Hom.onM g p.1 p.2 w) (EtaleSpecies.Hom.onM g p'.1 p'.2 w') := by
  cases h; cases hw; rfl

theorem heq_algHom_val_fam {ι : Type u} {A : ι → Type u} [∀ i, CommRing (A i)]
    [∀ i, Algebra K (A i)] {i i' : ι} (h : i = i')
    {φ : A i →ₐ[K] L} {ψ : A i' →ₐ[K] L} (hφ : HEq φ ψ)
    {a : A i} {a' : A i'} (ha : HEq a a') : φ a = ψ a' := by
  cases h; cases hφ; cases ha; rfl

theorem heq_famTransport {ι : Type u} (A : ι → Type u) [∀ i, CommRing (A i)]
    [∀ i, Algebra K (A i)] {i i' : ι} (h : i = i') (x : A i) :
    HEq x (famTransport (K := K) A h x) := by
  cases h; rfl

theorem counit_onM_val_aux {S T : EtaleSpecies.{u} K} (g : S ⟶ T)
    (EY : T.edgeSet L) (EX : S.edgeSet L) (σ : Gal(L/K))
    (hσ : σ • EX = EtaleSpecies.edgeMap g L EY)
    {cY : T.edgeIndexSet} (hY : cY = EY.1)
    {cX : S.edgeIndexSet} (hX : cX = EX.1)
    (z : S.M (EtaleSpecies.Hom.onI g cY.1.1) (EtaleSpecies.Hom.onI g cY.1.2))
    (z' : S.M cX.1.1 cX.1.2) (hzz : HEq z z') :
    EY.2 (residueFieldEquivOfEq hY (T.residueMap cY
        (EtaleSpecies.Hom.onM g cY.1.1 cY.1.2 z)))
      = σ (EX.2 (residueFieldEquivOfEq hX (S.residueMap cX z'))) := by
  cases hY
  cases hX
  have hsig : (⟨EX.1, σ • EX.2⟩ : S.edgeSet L)
      = ⟨⟨(EtaleSpecies.Hom.onI g EY.1.1.1, EtaleSpecies.Hom.onI g EY.1.1.2),
            kerMaximalSpectrum (EY.2.comp ((T.residueMap EY.1).comp
              (EtaleSpecies.Hom.onM g EY.1.1.1 EY.1.1.2)))⟩,
          S.kerResidueLift (EY.2.comp ((T.residueMap EY.1).comp
            (EtaleSpecies.Hom.onM g EY.1.1.1 EY.1.1.2)))⟩ := hσ
  have hidx := congrArg Sigma.fst hsig
  have hemb := sigma_heq_snd hsig
  have hz'' := heq_famTransport (K := K) (fun p : S.I × S.I => S.M p.1 p.2)
    (congrArg Sigma.fst hidx) z'
  have heqz : famTransport (K := K) (fun p : S.I × S.I => S.M p.1 p.2)
      (congrArg Sigma.fst hidx) z' = z := (eq_of_heq (hzz.trans hz'').symm)
  have hval := heq_algHom_apply_fam (A := fun c : S.edgeIndexSet => S.residueField c)
    (B := L) hidx hemb (heq_residueMap hidx hz'')
  exact (hval.trans (congrArg (fun w => EY.2 (T.residueMap EY.1
    (EtaleSpecies.Hom.onM g EY.1.1.1 EY.1.1.2 w))) heqz)).symm

theorem residueFieldEquivOfEq_residueMap {S : EtaleSpecies.{u} K} {c c' : S.edgeIndexSet}
    (h : c = c') {w : S.M c.1.1 c.1.2} {w' : S.M c'.1.1 c'.1.2} (hw : HEq w w') :
    residueFieldEquivOfEq h (S.residueMap c w) = S.residueMap c' w' := by
  cases h; cases hw; rfl


end HomInv

end EtaleSpecies

/-- **Clause `RQ2-2.13-H1`.** The category in which `Γ_K(−)` is defined: the full subcategory of
étale `K`-species split by `L`. The source's "`L` chosen large enough that all occurring finite
étale algebras split over `L`" is exactly this restriction, and the census marks it a
`JUSTIFIED_REFORMULATION` ("the choice of `L` is a proof device").

@census none (clause witness for `RQ2-2.13-H1`)
-/
abbrev SplitSpecies (K L : Type u) [Field K] [Field L] [Algebra K L] : Type (u + 1) :=
  (EtaleSpecies.splitBy K L).FullSubcategory

namespace SplitSpecies

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The `K`-rational quiver `Γ_K(X)` of a species split by `L`. -/
noncomputable def toQuiver (X : SplitSpecies K L) : RationalQuiver K L :=
  X.obj.toRationalQuiver L X.property

theorem vertexMap_source {X Y : SplitSpecies K L} (g : X ⟶ Y) (e : (toQuiver Y).E) :
    EtaleSpecies.vertexMap ((EtaleSpecies.splitBy K L).ι.map g) L
        ((toQuiver Y).toRQuiver.source e)
      = (toQuiver X).toRQuiver.source
          (EtaleSpecies.edgeMap ((EtaleSpecies.splitBy K L).ι.map g) L e) := by
  set G := (EtaleSpecies.splitBy K L).ι.map g with hG
  refine congrArg (Sigma.mk _) (AlgHom.ext fun x => ?_)
  exact congrArg (fun z => e.2 (Y.obj.residueMap e.1 z))
    (AlgHom.ext_iff.mp (G.compat_left e.1.1.1 e.1.1.2) x).symm

theorem vertexMap_target {X Y : SplitSpecies K L} (g : X ⟶ Y) (e : (toQuiver Y).E) :
    EtaleSpecies.vertexMap ((EtaleSpecies.splitBy K L).ι.map g) L
        ((toQuiver Y).toRQuiver.target e)
      = (toQuiver X).toRQuiver.target
          (EtaleSpecies.edgeMap ((EtaleSpecies.splitBy K L).ι.map g) L e) := by
  set G := (EtaleSpecies.splitBy K L).ι.map g with hG
  refine congrArg (Sigma.mk _) (AlgHom.ext fun x => ?_)
  exact congrArg (fun z => e.2 (Y.obj.residueMap e.1 z))
    (AlgHom.ext_iff.mp (G.compat_right e.1.1.1 e.1.1.2) x).symm

theorem vertexMap_equivariant {X Y : SplitSpecies K L} (g : X ⟶ Y) (σ : Gal(L/K))
    (v : (toQuiver Y).V) :
    EtaleSpecies.vertexMap ((EtaleSpecies.splitBy K L).ι.map g) L (σ • v)
      = σ • EtaleSpecies.vertexMap ((EtaleSpecies.splitBy K L).ι.map g) L v := rfl

theorem edgeMap_equivariant {X Y : SplitSpecies K L} (g : X ⟶ Y) (σ : Gal(L/K))
    (e : (toQuiver Y).E) :
    EtaleSpecies.edgeMap ((EtaleSpecies.splitBy K L).ι.map g) L (σ • e)
      = σ • EtaleSpecies.edgeMap ((EtaleSpecies.splitBy K L).ι.map g) L e := by
  set G := (EtaleSpecies.splitBy K L).ι.map g with hG
  refine EtaleSpecies.edgeSet_ext_of_val ?_ (fun x => rfl)
  refine MaximalSpectrum.ext ?_
  exact EtaleSpecies.ker_smul_comp
    (e.2.comp ((Y.obj.residueMap e.1).comp (G.onM e.1.1.1 e.1.1.2))) σ

/-- **Clause `RQ2-2.13-C2`.** `Γ_K(g) : Γ_K(Y) ⟶ Γ_K(X)`, the morphism of `K`-rational quivers
induced by `g : X ⟶ Y`.

Proof plan (G4) for the four obligations above: on vertices everything is precomposition while the
Galois action is postcomposition, so both compatibilities are associativity of composition; on
edges, `s(τ) = τ ∘ τ_ε` and the structure maps commute with `g.onM` by `compat_left`/`compat_right`
of `RQ2-2.04`, and equivariance needs `ker (σ ∘ φ) = ker φ` (`σ` is injective) together with the
transport of the residue lift along that equality — the one place in this stage where a
`Sigma`/`HEq` transport is unavoidable, exactly as S3 predicted for `RQ2-2.34`.

@census none (clause witness for `RQ2-2.13-C2`)
-/
noncomputable def toQuiverMap {X Y : SplitSpecies K L} (g : X ⟶ Y) :
    toQuiver Y ⟶ toQuiver X where
  toRQuiverHom :=
    { onV := EtaleSpecies.vertexMap ((EtaleSpecies.splitBy K L).ι.map g) L
      onE := EtaleSpecies.edgeMap ((EtaleSpecies.splitBy K L).ι.map g) L
      onV_source := vertexMap_source g
      onV_target := vertexMap_target g }
  equivariant_V := vertexMap_equivariant g
  equivariant_E := edgeMap_equivariant g

/-- Functoriality of `Γ_K(−)`, identity half. -/
theorem toQuiverMap_id (X : SplitSpecies K L) : toQuiverMap (𝟙 X) = 𝟙 (toQuiver X) := by
  refine RationalQuiver.Hom.ext (RQuiver.Hom.ext rfl (funext fun e => ?_))
  exact EtaleSpecies.edgeSet_ext_of_val
    (MaximalSpectrum.ext (EtaleSpecies.ker_comp_residueMap X.obj e.1 e.2)) (fun x => rfl)

/-- Functoriality of `Γ_K(−)`, composition half — with the reversal that makes `Γ_K(−)`
**contravariant**. -/
theorem toQuiverMap_comp {X Y Z : SplitSpecies K L} (g : X ⟶ Y) (h : Y ⟶ Z) :
    toQuiverMap (g ≫ h) = toQuiverMap h ≫ toQuiverMap g :=
  RationalQuiver.Hom.ext (RQuiver.Hom.ext rfl rfl)

end SplitSpecies

open CategoryTheory in
/-- **Clause `RQ2-2.13-C2`.** `Γ_K(−)` as a **contravariant** functor from the étale `K`-species
split by `L` to `K`-rational quivers.

@census none (clause witness for `RQ2-2.13-C2`)
-/
noncomputable def toQuiverFunctor (K L : Type u) [Field K] [Field L] [Algebra K L] :
    (SplitSpecies K L)ᵒᵖ ⥤ RationalQuiver K L where
  obj X := SplitSpecies.toQuiver X.unop
  map g := SplitSpecies.toQuiverMap g.unop
  map_id X := by
    show SplitSpecies.toQuiverMap (𝟙 X.unop) = _
    rw [SplitSpecies.toQuiverMap_id]
  map_comp f g := by
    show SplitSpecies.toQuiverMap (g.unop ≫ f.unop) = _
    rw [SplitSpecies.toQuiverMap_comp]

/-! ## The unit: `Γ_K → Γ_K(S(Γ_K))` (clause `RQ2-2.13-C3`) -/

namespace RationalQuiver

open MulAction

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

/-- **Clause `RQ2-2.13-H1`.** `S(Γ_K)` is split by `L`: its vertex and edge fields are intermediate
fields of the Galois extension `L/K`, so `L` splits their minimal polynomials, and its edge algebras
are finite products of such fields.

Proof plan (G4): for `α` in an intermediate field `E` of `L/K`, `minpoly K α` splits in `L` because
`L/K` is normal and `α ∈ L` (`IsGalois.splits`, `Normal.splits`); for the edge algebras, the minimal
polynomial of a tuple divides the product of the components' minimal polynomials, each of which
splits.

@census none (clause witness for `RQ2-2.13-H1`)
-/
theorem toSpecies_isSplitBy (Γ : RationalQuiver K L) : (Γ.toSpecies).IsSplitBy L where
  splits_L i x := splits_minpoly_intermediateField (Γ.vertexOrbitField i) x
  splits_M i j m := splits_minpoly_pi (fun ε => Γ.edgeOrbitField ε) m

/-- `S(Γ_K)` as an object of the category in which `Γ_K(−)` is defined. -/
noncomputable def toSplitSpecies (Γ : RationalQuiver K L) : SplitSpecies K L :=
  ⟨Γ.toSpecies, toSpecies_isSplitBy Γ⟩

/-- The embedding `L(v) ↪ L` attached to a vertex `v`, read as an element of
`Hom_K(L_{[v]}, L)`: it is the canonical orbit isomorphism `L_{[v]} ≅ L(v)` followed by the
inclusion `L(v) ⊆ L`. This is the paper's `Φ_V(v) : α ↦ τ α` for `τ` with `τ v_{[v]} = v`, and it
does not depend on `τ` by `stabField_apply_eq_of_smul_eq`.

@census none (clause witness for `RQ2-2.13-C3`)
-/
noncomputable def unitEmb (Γ : RationalQuiver K L) (v : Γ.V) :
    Γ.vertexOrbitField (Γ.vertexClass v) →ₐ[K] L :=
  (stabField K L v).val.comp (stabFieldEquivOrbit (Γ.mem_orbit_vertexRep v)).toAlgHom

/-- The edge analogue of `unitEmb`: the `K`-algebra map `{}_iM_j → L` attached to an edge `e`,
namely evaluation at the orbit of `e` followed by the embedding `L(e) ↪ L` twisted by the group
element carrying the chosen representative to `e`.

@census none (clause witness for `RQ2-2.13-C3`)
-/
noncomputable def unitEdgeEmb (Γ : RationalQuiver K L) {i j : Γ.VertexOrbit}
    (x : Γ.edgeSet i j) : Γ.toSpecies.M i j →ₐ[K] L :=
  ((stabField K L (x : Γ.E)).val.comp
      (stabFieldEquivOrbit (Γ.mem_orbit_edgeRep x)).toAlgHom).comp
    (Pi.evalAlgHom K _ (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet i j)) x))

/-- The value of `φ_e` in `L`: the chosen group element applied to the `ε`-component. The edge
analogue of `speciesMapOnL_coe`, and the equation every `Φ_E` computation runs through.

@census none (helper for clause `RQ2-2.13-C3`)
-/
theorem unitEdgeEmb_coe {Γ : RationalQuiver K L} {i j : Γ.VertexOrbit} (x : Γ.edgeSet i j)
    (z : Γ.toSpecies.M i j) :
    Γ.unitEdgeEmb x z
      = (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep x)).choose
          ((z (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet i j)) x) : L)) := by
  show ((stabFieldEquivOrbit (Γ.mem_orbit_edgeRep x))
      (z (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet i j)) x)) : L) = _
  rw [stabFieldEquivOrbit_coe]

/-- **The transport tool for the summit proofs.** Two vertices of `Γ_K(S(Γ_K))` are equal as soon
as their index components agree and their embeddings agree *on underlying elements of `L`*. Stating
it this way is what keeps the `Sigma`/`HEq` transport inside one lemma instead of at every call
site: the hypothesis quantifies over `a : L` together with its two membership proofs, so a consumer
never writes `▸`.

@census none (helper for clauses `RQ2-2.13-C1`, `C3`)
-/
theorem vertexSet_ext_of_val {Γ : RationalQuiver K L} {i j : Γ.VertexOrbit}
    {φ : Γ.vertexOrbitField i →ₐ[K] L} {ψ : Γ.vertexOrbitField j →ₐ[K] L} (h1 : i = j)
    (h2 : ∀ (a : L) (ha : a ∈ Γ.vertexOrbitField i) (hb : a ∈ Γ.vertexOrbitField j),
      φ ⟨a, ha⟩ = ψ ⟨a, hb⟩) :
    (⟨i, φ⟩ : Γ.toSpecies.vertexSet L) = ⟨j, ψ⟩ := by
  cases h1
  exact congrArg (Sigma.mk i) (AlgHom.ext fun x => h2 x x.2 x.2)

/-- The paper's `Φ_V`: a vertex `v` goes to the embedding `L_{[v]} → L` it induces. -/
noncomputable def unitOnV (Γ : RationalQuiver K L) :
    Γ.V → (SplitSpecies.toQuiver (toSplitSpecies Γ)).V :=
  fun v => ⟨Γ.vertexClass v, Γ.unitEmb v⟩

/-- The paper's `Φ_E`. -/
noncomputable def unitOnE (Γ : RationalQuiver K L) :
    Γ.E → (SplitSpecies.toQuiver (toSplitSpecies Γ)).E :=
  fun e =>
    ⟨⟨(Γ.vertexClass (Γ.toRQuiver.source e), Γ.vertexClass (Γ.toRQuiver.target e)),
        EtaleSpecies.kerMaximalSpectrum
          (A := Γ.toSpecies.M (Γ.vertexClass (Γ.toRQuiver.source e))
            (Γ.vertexClass (Γ.toRQuiver.target e)))
          (Γ.unitEdgeEmb ⟨e, ⟨rfl, rfl⟩⟩)⟩,
      EtaleSpecies.kerResidueLift Γ.toSpecies (Γ.unitEdgeEmb ⟨e, ⟨rfl, rfl⟩⟩)⟩

/-- `Φ_V ∘ s = s' ∘ Φ_E`: the source's "Compatibility with source and target maps" paragraph.

Proof plan (G4): `s'(Φ_E(e)) = Φ_E(e) ∘ τ_ε`, and on `α ∈ L_i` both sides are `σ α` for the `σ`
carrying the chosen representative to `e`; the source's own computation.

@census none (clause witness for `RQ2-2.13-C3`)
-/
theorem unitOnV_source (Γ : RationalQuiver K L) (e : Γ.E) :
    Γ.unitOnV (Γ.toRQuiver.source e)
      = (SplitSpecies.toQuiver (toSplitSpecies Γ)).toRQuiver.source (Γ.unitOnE e) := by
  refine vertexSet_ext_of_val rfl ?_
  intro a ha _
  have he : e ∈ Γ.edgeSet (Γ.vertexClass (Γ.toRQuiver.source e))
      (Γ.vertexClass (Γ.toRQuiver.target e)) := ⟨rfl, rfl⟩
  set ε₀ := Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet (Γ.vertexClass (Γ.toRQuiver.source e))
    (Γ.vertexClass (Γ.toRQuiver.target e)))) (⟨e, he⟩ : Γ.edgeSet _ _)
  set τ := (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep (Γ.toRQuiver.source e))).choose
  set ρ := (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep (⟨e, he⟩ : Γ.edgeSet _ _))).choose
  set σ' := (mem_orbit_iff.mp (Γ.source_edgeRep_mem_orbit ε₀)).choose
  have eτ : τ • Γ.vertexRep (Γ.vertexClass (Γ.toRQuiver.source e)) = Γ.toRQuiver.source e :=
    (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep (Γ.toRQuiver.source e))).choose_spec
  have eρ : ρ • Γ.edgeRep ε₀ = e :=
    (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep (⟨e, he⟩ : Γ.edgeSet _ _))).choose_spec
  have eσ' : σ' • Γ.vertexRep (Γ.vertexClass (Γ.toRQuiver.source e))
      = Γ.toRQuiver.source (Γ.edgeRep ε₀) :=
    (mem_orbit_iff.mp (Γ.source_edgeRep_mem_orbit ε₀)).choose_spec
  have key : τ • Γ.vertexRep (Γ.vertexClass (Γ.toRQuiver.source e))
      = (ρ * σ') • Γ.vertexRep (Γ.vertexClass (Γ.toRQuiver.source e)) := by
    rw [eτ, mul_smul, eσ', ← Γ.source_smul, eρ]
  have hval := stabField_apply_eq_of_smul_eq (σ := τ) (τ := ρ * σ') key ⟨a, ha⟩
  show τ a = ρ (σ' a)
  simpa [AlgEquiv.mul_apply] using hval

/-- `Φ_V ∘ t = t' ∘ Φ_E`.

@census none (clause witness for `RQ2-2.13-C3`)
-/
theorem unitOnV_target (Γ : RationalQuiver K L) (e : Γ.E) :
    Γ.unitOnV (Γ.toRQuiver.target e)
      = (SplitSpecies.toQuiver (toSplitSpecies Γ)).toRQuiver.target (Γ.unitOnE e) := by
  refine vertexSet_ext_of_val rfl ?_
  intro a ha _
  have he : e ∈ Γ.edgeSet (Γ.vertexClass (Γ.toRQuiver.source e))
      (Γ.vertexClass (Γ.toRQuiver.target e)) := ⟨rfl, rfl⟩
  set ε₀ := Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet (Γ.vertexClass (Γ.toRQuiver.source e))
    (Γ.vertexClass (Γ.toRQuiver.target e)))) (⟨e, he⟩ : Γ.edgeSet _ _)
  set τ := (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep (Γ.toRQuiver.target e))).choose
  set ρ := (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep (⟨e, he⟩ : Γ.edgeSet _ _))).choose
  set σ' := (mem_orbit_iff.mp (Γ.target_edgeRep_mem_orbit ε₀)).choose
  have eτ : τ • Γ.vertexRep (Γ.vertexClass (Γ.toRQuiver.target e)) = Γ.toRQuiver.target e :=
    (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep (Γ.toRQuiver.target e))).choose_spec
  have eρ : ρ • Γ.edgeRep ε₀ = e :=
    (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep (⟨e, he⟩ : Γ.edgeSet _ _))).choose_spec
  have eσ' : σ' • Γ.vertexRep (Γ.vertexClass (Γ.toRQuiver.target e))
      = Γ.toRQuiver.target (Γ.edgeRep ε₀) :=
    (mem_orbit_iff.mp (Γ.target_edgeRep_mem_orbit ε₀)).choose_spec
  have key : τ • Γ.vertexRep (Γ.vertexClass (Γ.toRQuiver.target e))
      = (ρ * σ') • Γ.vertexRep (Γ.vertexClass (Γ.toRQuiver.target e)) := by
    rw [eτ, mul_smul, eσ', ← Γ.target_smul, eρ]
  have hval := stabField_apply_eq_of_smul_eq (σ := τ) (τ := ρ * σ') key ⟨a, ha⟩
  show τ a = ρ (σ' a)
  simpa [AlgEquiv.mul_apply] using hval

/-- `Φ_V` is `Gal(L/K)`-equivariant: the source's "`Φ_V(σ v)` is the map `α ↦ στα`, which is
precisely `σ Φ_V(v)`".

@census none (clause witness for `RQ2-2.13-C3`)
-/
theorem unitOnV_equivariant (Γ : RationalQuiver K L) (σ : Gal(L/K)) (v : Γ.V) :
    Γ.unitOnV (σ • v) = σ • Γ.unitOnV v := by
  have h1 : Γ.vertexClass (σ • v) = Γ.vertexClass v := Quotient.sound (mem_orbit _ σ)
  refine vertexSet_ext_of_val h1 ?_
  intro a ha _
  have hrep : Γ.vertexRep (Γ.vertexClass (σ • v)) = Γ.vertexRep (Γ.vertexClass v) :=
    congrArg Γ.vertexRep h1
  set τ₁ := (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep (σ • v))).choose
  set τ₂ := (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep v)).choose
  have e₁ : τ₁ • Γ.vertexRep (Γ.vertexClass (σ • v)) = σ • v :=
    (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep (σ • v))).choose_spec
  have e₂ : τ₂ • Γ.vertexRep (Γ.vertexClass v) = v :=
    (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep v)).choose_spec
  have key : τ₁ • Γ.vertexRep (Γ.vertexClass (σ • v))
      = (σ * τ₂) • Γ.vertexRep (Γ.vertexClass (σ • v)) := by
    rw [e₁, hrep, mul_smul, e₂]
  have hval := stabField_apply_eq_of_smul_eq (σ := τ₁) (τ := σ * τ₂) key ⟨a, ha⟩
  show τ₁ a = σ (τ₂ a)
  simpa [AlgEquiv.mul_apply] using hval

/-- `HEq` of two algebra maps out of intermediate fields, evaluated: the version
`unitOnV_bijective` needs, where the `Sigma` equality hands out an `HEq` and the consumer wants an
equation on elements of `L`.

@census none (helper for clause `RQ2-2.13-C4`)
-/
theorem heq_algHom_val {E F : IntermediateField K L} {A : Type u} [Semiring A] [Algebra K A]
    {φ : E →ₐ[K] A} {ψ : F →ₐ[K] A} (hEF : E = F) (h : HEq φ ψ)
    (a : L) (ha : a ∈ E) (hb : a ∈ F) : φ ⟨a, ha⟩ = ψ ⟨a, hb⟩ := by
  cases hEF; cases h; rfl

/-- The value of `φ_v` in `L`: the chosen group element carrying `v_{[v]}` to `v`.

@census none (helper for clause `RQ2-2.13-C4`)
-/
theorem unitEmb_coe (Γ : RationalQuiver K L) (v : Γ.V)
    (α : Γ.vertexOrbitField (Γ.vertexClass v)) :
    Γ.unitEmb v α = (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep v)).choose (α : L) := by
  show ((stabFieldEquivOrbit (Γ.mem_orbit_vertexRep v) α : L)) = _
  rw [stabFieldEquivOrbit_coe]

/-- **Clause `RQ2-2.13-C4`, vertices.** `Φ_V : V → ⨆_i Hom_K(L_i,L)` is a **bijection**.

Injectivity is `smul_eq_of_stabField_apply_eq`: if `φ_v = φ_w` then the two chosen group elements
agree on `L_{[v]}`, hence move `v_{[v]}` the same way, hence `v = w`. Surjectivity is
`exists_galois_comp_eq` (`MD-S4-01`): any `τ : L_i → L` differs from the inclusion by some
`σ ∈ Gal(L/K)`, and then `σ v_i` is a preimage. Together they are the source's "`V` is the disjoint
union of the `Hom_K(L_i,L)`".

@census none (clause witness for `RQ2-2.13-C4`)
-/
theorem unitOnV_bijective (Γ : RationalQuiver K L) : Function.Bijective Γ.unitOnV := by
  constructor
  · intro v w hvw
    have hvw' : (⟨Γ.vertexClass v, Γ.unitEmb v⟩ : Γ.toSpecies.vertexSet L)
        = ⟨Γ.vertexClass w, Γ.unitEmb w⟩ := hvw
    rw [Sigma.mk.injEq] at hvw'
    obtain ⟨hc, hE⟩ := hvw'
    have hrep : Γ.vertexRep (Γ.vertexClass v) = Γ.vertexRep (Γ.vertexClass w) :=
      congrArg Γ.vertexRep hc
    have ev := (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep v)).choose_spec
    have ew := (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep w)).choose_spec
    have hagree : ∀ α : stabField K L (Γ.vertexRep (Γ.vertexClass v)),
        (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep v)).choose (α : L)
          = (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep w)).choose (α : L) := by
      intro α
      have hb : (α : L) ∈ Γ.vertexOrbitField (Γ.vertexClass w) := by
        rw [← hc]; exact α.2
      rw [← unitEmb_coe Γ v α, ← unitEmb_coe Γ w ⟨(α : L), hb⟩]
      exact heq_algHom_val (congrArg Γ.vertexOrbitField hc) hE (α : L) α.2 hb
    have hkey := smul_eq_of_stabField_apply_eq (Γ.isOpen_stabilizer_V _) hagree
    rw [ev, hrep, ew] at hkey
    exact hkey
  · rintro ⟨i, τ⟩
    obtain ⟨σ, hσ⟩ := EtaleSpecies.exists_galois_comp_eq L (Γ.vertexOrbitField i)
      (Γ.vertexOrbitField i).val τ
    refine ⟨σ • Γ.vertexRep i, ?_⟩
    have hc : Γ.vertexClass (σ • Γ.vertexRep i) = i := by
      rw [show Γ.vertexClass (σ • Γ.vertexRep i) = Γ.vertexClass (Γ.vertexRep i) from
        Quotient.sound (mem_orbit _ σ), Γ.vertexClass_vertexRep]
    refine vertexSet_ext_of_val hc ?_
    intro a ha hb
    rw [unitEmb_coe]
    have hspec := (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep (σ • Γ.vertexRep i))).choose_spec
    have hsm : (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep (σ • Γ.vertexRep i))).choose
          • Γ.vertexRep (Γ.vertexClass (σ • Γ.vertexRep i))
        = σ • Γ.vertexRep (Γ.vertexClass (σ • Γ.vertexRep i)) := by
      rw [hspec, hc]
    have hval := stabField_apply_eq_of_smul_eq hsm ⟨a, ha⟩
    rw [hval]
    exact (congrArg (fun f : Γ.vertexOrbitField i →ₐ[K] L => f ⟨a, hb⟩) hσ)

/-- `Φ_E` is `Gal(L/K)`-equivariant.

@census none (clause witness for `RQ2-2.13-C3`)
-/
theorem unitOnE_equivariant (Γ : RationalQuiver K L) (σ : Gal(L/K)) (e : Γ.E) :
    Γ.unitOnE (σ • e) = σ • Γ.unitOnE e := by
  have hs : Γ.vertexClass (Γ.toRQuiver.source (σ • e))
      = Γ.vertexClass (Γ.toRQuiver.source e) := by
    rw [Γ.source_smul]; exact Quotient.sound (mem_orbit _ σ)
  have ht : Γ.vertexClass (Γ.toRQuiver.target (σ • e))
      = Γ.vertexClass (Γ.toRQuiver.target e) := by
    rw [Γ.target_smul]; exact Quotient.sound (mem_orbit _ σ)
  have he₂ : e ∈ Γ.edgeSet (Γ.vertexClass (Γ.toRQuiver.source e))
      (Γ.vertexClass (Γ.toRQuiver.target e)) := ⟨rfl, rfl⟩
  have he₁ : σ • e ∈ Γ.edgeSet (Γ.vertexClass (Γ.toRQuiver.source (σ • e)))
      (Γ.vertexClass (Γ.toRQuiver.target (σ • e))) := ⟨rfl, rfl⟩
  refine EtaleSpecies.edgeSet_ext_of_emb (Prod.ext hs ht) ?_
  intro x y hxy
  have hcls : HEq (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _)) (⟨σ • e, he₁⟩ : Γ.edgeSet _ _))
      (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _)) (⟨e, he₂⟩ : Γ.edgeSet _ _)) :=
    heq_edgeOrbit_mk_smul hs ht σ e he₁ he₂
  have hrep : Γ.edgeRep (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
        (⟨σ • e, he₁⟩ : Γ.edgeSet _ _))
      = Γ.edgeRep (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
        (⟨e, he₂⟩ : Γ.edgeSet _ _)) :=
    edgeRep_heq_congr hs ht hcls
  have hval : ((x (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
        (⟨σ • e, he₁⟩ : Γ.edgeSet _ _)) : L))
      = (y (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
        (⟨e, he₂⟩ : Γ.edgeSet _ _)) : L) :=
    edgeAlgebra_apply_val_congr hs ht hxy hcls
  have e₁ := (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep (⟨σ • e, he₁⟩ : Γ.edgeSet _ _))).choose_spec
  have e₂ := (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep (⟨e, he₂⟩ : Γ.edgeSet _ _))).choose_spec
  have key : (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep (⟨σ • e, he₁⟩ : Γ.edgeSet _ _))).choose
        • Γ.edgeRep (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
            (⟨σ • e, he₁⟩ : Γ.edgeSet _ _))
      = (σ * (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep (⟨e, he₂⟩ : Γ.edgeSet _ _))).choose)
        • Γ.edgeRep (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
            (⟨σ • e, he₁⟩ : Γ.edgeSet _ _)) := by
    rw [e₁, mul_smul, hrep, e₂]
  have hstab := stabField_apply_eq_of_smul_eq key
    (x (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _)) (⟨σ • e, he₁⟩ : Γ.edgeSet _ _)))
  show Γ.unitEdgeEmb (⟨σ • e, he₁⟩ : Γ.edgeSet _ _) x
      = σ (Γ.unitEdgeEmb (⟨e, he₂⟩ : Γ.edgeSet _ _) y)
  rw [unitEdgeEmb_coe, unitEdgeEmb_coe, hstab, AlgEquiv.mul_apply, hval]

/-- **Clause `RQ2-2.13-C4`, edges (surjectivity).** Every pair `(ε, τ)` with `ε ∈ Specm {}_iM_j` and
`τ : L_ε → L` is `Φ_E` of an edge.

The proof is the edge analogue of `unitOnV_bijective`'s surjectivity, with one extra step in front:
`{}_iM_j` is a finite product of fields, so the composite `L_ε → L` precomposed with the residue
map factors through exactly one projection (`exists_pi_factor`), which names the edge orbit `ε₀`;
`exists_galois_comp_eq` (`MD-S4-01`) then writes the resulting embedding `L(e_{ε₀}) → L` as the
restriction of some `σ ∈ Gal(L/K)`, and `σ e_{ε₀}` is the preimage. `edgeSet_ext_of_emb` does the
`Σ`-transport, and the maximal ideal is forced by it rather than computed.

@census none (clause witness for `RQ2-2.13-C4`)
-/
theorem unitOnE_surjective (Γ : RationalQuiver K L) : Function.Surjective Γ.unitOnE := by
  rintro ⟨⟨⟨i, j⟩, m⟩, τ⟩
  obtain ⟨ε₀, ĝ, hg⟩ := EtaleSpecies.exists_pi_factor (K := K) (ι := Γ.EdgeOrbit i j)
      (F := fun ε => (Γ.edgeOrbitField ε : Type u)) (B := L)
      (τ.comp (Γ.toSpecies.residueMap ⟨(i, j), m⟩))
  obtain ⟨σ, hσ⟩ := EtaleSpecies.exists_galois_comp_eq L (Γ.edgeOrbitField ε₀)
      (Γ.edgeOrbitField ε₀).val ĝ
  refine ⟨σ • Γ.edgeRep ε₀, ?_⟩
  have hs : Γ.vertexClass (Γ.toRQuiver.source (σ • Γ.edgeRep ε₀)) = i := by
    rw [Γ.source_smul, show Γ.vertexClass (σ • Γ.toRQuiver.source (Γ.edgeRep ε₀))
      = Γ.vertexClass (Γ.toRQuiver.source (Γ.edgeRep ε₀)) from Quotient.sound (mem_orbit _ σ)]
    exact Γ.vertexClass_source_edgeRep ε₀
  have ht : Γ.vertexClass (Γ.toRQuiver.target (σ • Γ.edgeRep ε₀)) = j := by
    rw [Γ.target_smul, show Γ.vertexClass (σ • Γ.toRQuiver.target (Γ.edgeRep ε₀))
      = Γ.vertexClass (Γ.toRQuiver.target (Γ.edgeRep ε₀)) from Quotient.sound (mem_orbit _ σ)]
    exact Γ.vertexClass_target_edgeRep ε₀
  have heij : σ • Γ.edgeRep ε₀ ∈ Γ.edgeSet i j := ⟨hs, ht⟩
  have hcls0 : (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet i j))
      (⟨σ • Γ.edgeRep ε₀, heij⟩ : Γ.edgeSet i j)) = ε₀ := by
    have h1 : (⟨σ • Γ.edgeRep ε₀, heij⟩ : Γ.edgeSet i j) = σ • (Quotient.out ε₀) :=
      Subtype.ext rfl
    rw [h1, Quotient.sound (mem_orbit (Quotient.out ε₀) σ), Quotient.out_eq]
  have hcls : HEq (Quotient.mk (orbitRel Gal(L/K)
        (Γ.edgeSet (Γ.vertexClass (Γ.toRQuiver.source (σ • Γ.edgeRep ε₀)))
          (Γ.vertexClass (Γ.toRQuiver.target (σ • Γ.edgeRep ε₀)))))
        (⟨σ • Γ.edgeRep ε₀, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _)) ε₀ :=
    (heq_edgeOrbit_mk hs ht (σ • Γ.edgeRep ε₀) ⟨rfl, rfl⟩ heij).trans (heq_of_eq hcls0)
  refine EtaleSpecies.edgeSet_ext_of_emb (Prod.ext hs ht) ?_
  intro x y hxy
  have hval : ((x (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
        (⟨σ • Γ.edgeRep ε₀, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _)) : L)) = (y ε₀ : L) :=
    edgeAlgebra_apply_val_congr hs ht hxy hcls
  have hrep : Γ.edgeRep (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
        (⟨σ • Γ.edgeRep ε₀, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _)) = Γ.edgeRep ε₀ :=
    edgeRep_heq_congr hs ht hcls
  have hspec := (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep
    (⟨σ • Γ.edgeRep ε₀, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _))).choose_spec
  have hsm : (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep
        (⟨σ • Γ.edgeRep ε₀, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _))).choose
        • Γ.edgeRep (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
            (⟨σ • Γ.edgeRep ε₀, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _))
      = σ • Γ.edgeRep (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
            (⟨σ • Γ.edgeRep ε₀, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _)) := by
    rw [hspec, hrep]
  have hA : Γ.unitEdgeEmb (⟨σ • Γ.edgeRep ε₀, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _) x
      = (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep
          (⟨σ • Γ.edgeRep ε₀, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _))).choose
        ((x (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
          (⟨σ • Γ.edgeRep ε₀, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _)) : L)) :=
    unitEdgeEmb_coe _ _
  have hB : (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep
          (⟨σ • Γ.edgeRep ε₀, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _))).choose
        ((x (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
          (⟨σ • Γ.edgeRep ε₀, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _)) : L))
      = σ ((x (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
          (⟨σ • Γ.edgeRep ε₀, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _)) : L)) :=
    stabField_apply_eq_of_smul_eq hsm _
  have hC : σ ((x (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
          (⟨σ • Γ.edgeRep ε₀, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _)) : L)) = σ ((y ε₀ : L)) :=
    congrArg (fun z : L => σ z) hval
  have hD : τ (Γ.toSpecies.residueMap (⟨(i, j), m⟩) y) = ĝ (y ε₀) :=
    congrArg (fun f : Γ.toSpecies.M i j →ₐ[K] L => f y) hg
  have hE : ĝ ((y ε₀)) = σ ((y ε₀ : L)) :=
    (congrArg (fun f : Γ.edgeOrbitField ε₀ →ₐ[K] L => f (y ε₀)) hσ).symm
  exact (hA.trans (hB.trans hC)).trans (hD.trans hE).symm

/-- **Clause `RQ2-2.13-C3`.** The canonical morphism `Γ_K ⟶ Γ_K(S(Γ_K))` of `K`-rational quivers:
the paper's `(Φ_V, Φ_E)`.

@census none (clause witness for `RQ2-2.13-C3`)
-/
noncomputable def unitApp (Γ : RationalQuiver K L) :
    Γ ⟶ SplitSpecies.toQuiver (toSplitSpecies Γ) where
  toRQuiverHom :=
    { onV := Γ.unitOnV
      onE := Γ.unitOnE
      onV_source := Γ.unitOnV_source
      onV_target := Γ.unitOnV_target }
  equivariant_V := Γ.unitOnV_equivariant
  equivariant_E := Γ.unitOnE_equivariant

/-! ### `Φ_E` is injective, and the unit is an isomorphism (clause `RQ2-2.13-C4`) -/

/-- Two edge orbits at which two Galois elements induce the same map on `{}_iM_j` are equal: test
on the idempotent `Pi.single ε 1`, which the first sees as `1` and the second, if the orbits
differed, as `0`.

@census none (helper for clause `RQ2-2.13-C4`)
-/
theorem edgeOrbit_eq_of_agree {Γ : RationalQuiver K L} {i j : Γ.VertexOrbit}
    {εe εf : Γ.EdgeOrbit i j} {ρe ρf : Gal(L/K)}
    (hagree : ∀ x : Γ.edgeAlgebra i j, ρe ((x εe : L)) = ρf ((x εf : L))) : εe = εf := by
  classical
  by_contra hne
  have h1 := hagree (Pi.single εe 1)
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at h1
  simp at h1

theorem gal_agree_of_agree {Γ : RationalQuiver K L} {i j : Γ.VertexOrbit}
    {εe εf : Γ.EdgeOrbit i j} {ρe ρf : Gal(L/K)}
    (hagree : ∀ x : Γ.edgeAlgebra i j, ρe ((x εe : L)) = ρf ((x εf : L)))
    (hcls : εe = εf) (α : stabField K L (Γ.edgeRep εe)) : ρe (α : L) = ρf (α : L) := by
  classical
  have h1 := hagree (Pi.single εe (α : Γ.edgeOrbitField εe))
  rw [Pi.single_eq_same, ← hcls, Pi.single_eq_same] at h1
  exact h1

theorem unitOnE_inj_core {Γ : RationalQuiver K L} {s₁ s₂ t₁ t₂ : Γ.VertexOrbit}
    (hs : s₁ = s₂) (ht : t₁ = t₂) {e f : Γ.E}
    (he : e ∈ Γ.edgeSet s₁ t₁) (hf : f ∈ Γ.edgeSet s₂ t₂)
    (hagree : ∀ (x : Γ.edgeAlgebra s₁ t₁) (y : Γ.edgeAlgebra s₂ t₂), HEq x y →
      Γ.unitEdgeEmb ⟨e, he⟩ x = Γ.unitEdgeEmb ⟨f, hf⟩ y) : e = f := by
  cases hs; cases ht
  have hval : ∀ x : Γ.edgeAlgebra s₁ t₁,
      (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep (⟨e, he⟩ : Γ.edgeSet s₁ t₁))).choose
          ((x (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet s₁ t₁))
            (⟨e, he⟩ : Γ.edgeSet s₁ t₁)) : L))
        = (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep (⟨f, hf⟩ : Γ.edgeSet s₁ t₁))).choose
          ((x (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet s₁ t₁))
            (⟨f, hf⟩ : Γ.edgeSet s₁ t₁)) : L)) := fun x =>
    (Γ.unitEdgeEmb_coe _ _).symm.trans ((hagree x x HEq.rfl).trans (Γ.unitEdgeEmb_coe _ _))
  have hcls := edgeOrbit_eq_of_agree hval
  have hkey := smul_eq_of_stabField_apply_eq (Γ.isOpen_stabilizer_E _)
    (gal_agree_of_agree hval hcls)
  rw [(mem_orbit_iff.mp (Γ.mem_orbit_edgeRep (⟨e, he⟩ : Γ.edgeSet s₁ t₁))).choose_spec] at hkey
  rw [hcls,
    (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep (⟨f, hf⟩ : Γ.edgeSet s₁ t₁))).choose_spec] at hkey
  exact hkey


/-- A morphism of `K`-rational quivers whose two components are bijections is an isomorphism: the
inverse functions are again a morphism, because each defining equation can be checked after
applying the (injective) forward map.

@census none (helper for clause `RQ2-2.13-C4`)
-/
noncomputable def homInv {Γ Γ' : RationalQuiver K L} (φ : Γ ⟶ Γ')
    (hV : Function.Bijective φ.toRQuiverHom.onV)
    (hE : Function.Bijective φ.toRQuiverHom.onE) : Γ' ⟶ Γ where
  toRQuiverHom :=
    { onV := (Equiv.ofBijective _ hV).symm
      onE := (Equiv.ofBijective _ hE).symm
      onV_source := by
        intro e'
        refine hV.injective ?_
        rw [show ∀ v, φ.toRQuiverHom.onV ((Equiv.ofBijective _ hV).symm v) = v from
          fun v => (Equiv.ofBijective _ hV).apply_symm_apply v]
        rw [φ.toRQuiverHom.onV_source]
        exact (congrArg Γ'.toRQuiver.source ((Equiv.ofBijective _ hE).apply_symm_apply e')).symm
      onV_target := by
        intro e'
        refine hV.injective ?_
        rw [show ∀ v, φ.toRQuiverHom.onV ((Equiv.ofBijective _ hV).symm v) = v from
          fun v => (Equiv.ofBijective _ hV).apply_symm_apply v]
        rw [φ.toRQuiverHom.onV_target]
        exact (congrArg Γ'.toRQuiver.target ((Equiv.ofBijective _ hE).apply_symm_apply e')).symm }
  equivariant_V := by
    intro σ v
    refine hV.injective ?_
    rw [show ∀ w, φ.toRQuiverHom.onV ((Equiv.ofBijective _ hV).symm w) = w from
      fun w => (Equiv.ofBijective _ hV).apply_symm_apply w]
    rw [φ.equivariant_V]
    rw [show ∀ w, φ.toRQuiverHom.onV ((Equiv.ofBijective _ hV).symm w) = w from
      fun w => (Equiv.ofBijective _ hV).apply_symm_apply w]
  equivariant_E := by
    intro σ e
    refine hE.injective ?_
    rw [show ∀ w, φ.toRQuiverHom.onE ((Equiv.ofBijective _ hE).symm w) = w from
      fun w => (Equiv.ofBijective _ hE).apply_symm_apply w]
    rw [φ.equivariant_E]
    rw [show ∀ w, φ.toRQuiverHom.onE ((Equiv.ofBijective _ hE).symm w) = w from
      fun w => (Equiv.ofBijective _ hE).apply_symm_apply w]

theorem isIso_of_bijective {Γ Γ' : RationalQuiver K L} (φ : Γ ⟶ Γ')
    (hV : Function.Bijective φ.toRQuiverHom.onV)
    (hE : Function.Bijective φ.toRQuiverHom.onE) : IsIso φ := by
  refine ⟨homInv φ hV hE, ?_, ?_⟩
  · refine RationalQuiver.Hom.ext (RQuiver.Hom.ext ?_ ?_)
    · exact funext fun v => (Equiv.ofBijective _ hV).symm_apply_apply v
    · exact funext fun e => (Equiv.ofBijective _ hE).symm_apply_apply e
  · refine RationalQuiver.Hom.ext (RQuiver.Hom.ext ?_ ?_)
    · exact funext fun v => (Equiv.ofBijective _ hV).apply_symm_apply v
    · exact funext fun e => (Equiv.ofBijective _ hE).apply_symm_apply e


/-- **Clause `RQ2-2.13-C4`, edges.** `Φ_E` is a bijection. -/
theorem unitOnE_bijective (Γ : RationalQuiver K L) : Function.Bijective Γ.unitOnE := by
  refine ⟨?_, Γ.unitOnE_surjective⟩
  intro e f hef
  have hc := congrArg Sigma.fst hef
  have hp := congrArg Sigma.fst hc
  refine unitOnE_inj_core (congrArg Prod.fst hp) (congrArg Prod.snd hp)
    (⟨rfl, rfl⟩ : e ∈ Γ.edgeSet _ _) (⟨rfl, rfl⟩ : f ∈ Γ.edgeSet _ _) ?_
  intro x y hxy
  exact EtaleSpecies.edgeSet_val_of_eq hef hxy

/-- **Clause `RQ2-2.13-C4`.** The unit `Φ = (Φ_V, Φ_E) : Γ_K ⟶ Γ_K(S(Γ_K))` is an **isomorphism**
of `K`-rational quivers — the first conjunct of `speciesAntiEquivalence`.

@census none (clause witness for `RQ2-2.13-C4`)
-/
theorem unitApp_isIso (Γ : RationalQuiver K L) : IsIso (Γ.unitApp) :=
  isIso_of_bijective _ Γ.unitOnV_bijective Γ.unitOnE_bijective


end RationalQuiver

/-! ## The counit, the split objects, and the anti-equivalence (clauses `RQ2-2.13-C4`–`C7`) -/

open MulAction in
/-- **Clause `RQ2-2.13-C4`, index component.** The canonical map `I(Γ_K(S)) → I(S)`: an orbit of
vertices of `Γ_K(S)` is sent to the index its chosen representative lies over. By `RQ2-2.10` this is
a bijection, and it is `π` read on orbits; taking it at the chosen representative rather than as a
`Quotient.lift` is what makes the vertex-field component below type-check without a transport.

@census none (clause witness for `RQ2-2.13-C4`)
-/
noncomputable def counitOnI {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L) :
    (SplitSpecies.toQuiver X).VertexOrbit → X.obj.I :=
  fun t => ((SplitSpecies.toQuiver X).vertexRep t).1

/-- **Clause `RQ2-2.13-C4`, vertex-algebra component.** `L_{ι(t)} ≅ L_t`: the chosen representative
of the orbit `t` is an embedding `τ : L_{ι(t)} → L`, and by `stabField_vertexSet` its image is
exactly `L(v_t) = L_t`. This is the algebra half of the counit `S ⟶ S(Γ_K(S))`.

@census none (clause witness for `RQ2-2.13-C4`)
-/
noncomputable def counitOnL {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L)
    (t : (SplitSpecies.toQuiver X).VertexOrbit) :
    X.obj.L (counitOnI X t) ≃ₐ[K] (SplitSpecies.toQuiver X).toSpecies.L t :=
  (AlgEquiv.ofInjectiveField ((SplitSpecies.toQuiver X).vertexRep t).2).trans
    (IntermediateField.equivOfEq (X.obj.stabField_vertexSet _).symm)

theorem counitOnL_coe {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L)
    (t : (SplitSpecies.toQuiver X).VertexOrbit) (a : X.obj.L (counitOnI X t)) :
    (counitOnL X t a).val = ((SplitSpecies.toQuiver X).vertexRep t).2 a := rfl

/-- **Clause `RQ2-2.13-C4`, edge-algebra component, one summand.** `L_{ε(e)} ≅ L(e_ε)`: exactly as
for vertices, the chosen representative of the edge orbit `ε` is an embedding of the residue field
`L_{ε(e)}` into `L`, and `stabField_edgeSet` identifies its image with `L(e_ε)`.

@census none (clause witness for `RQ2-2.13-C4`)
-/
noncomputable def counitOnEdgeField {K L : Type u} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] (X : SplitSpecies K L)
    {s t : (SplitSpecies.toQuiver X).VertexOrbit}
    (ε : (SplitSpecies.toQuiver X).EdgeOrbit s t) :
    X.obj.residueField ((SplitSpecies.toQuiver X).edgeRep ε).1
      ≃ₐ[K] (SplitSpecies.toQuiver X).edgeOrbitField ε :=
  (AlgEquiv.ofInjectiveField ((SplitSpecies.toQuiver X).edgeRep ε).2).trans
    (IntermediateField.equivOfEq (X.obj.stabField_edgeSet _).symm)

theorem counitOnEdgeField_coe {K L : Type u} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] (X : SplitSpecies K L)
    {s t : (SplitSpecies.toQuiver X).VertexOrbit}
    (ε : (SplitSpecies.toQuiver X).EdgeOrbit s t)
    (a : X.obj.residueField ((SplitSpecies.toQuiver X).edgeRep ε).1) :
    (counitOnEdgeField X ε a).val = ((SplitSpecies.toQuiver X).edgeRep ε).2 a := rfl

/-! ### The per-pair restriction of `RQ2-2.10`/`RQ2-2.11`

`RQ2-2.10` says the orbit set of vertices of `Γ_K(S)` maps bijectively to `I(S)`, and `RQ2-2.11` says
the same for edges; what the counit's edge component needs is the *fibrewise* form: an edge of
`Γ_K(S)` lies in `E_{st}` exactly when its index pair is `(ι(s), ι(t))`. The lemmas below are that
reduction, stated so that nothing downstream has to reason about `vertexClass` again — only about
index components, where there is no quotient.
-/

theorem vertexOrbitProj_eq_counitOnI {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L)
    (s : (SplitSpecies.toQuiver X).VertexOrbit) :
    EtaleSpecies.vertexOrbitProj X.obj L s = counitOnI X s := by
  conv_lhs => rw [← (SplitSpecies.toQuiver X).vertexClass_vertexRep s]
  rfl

theorem vertexClass_eq_iff {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L)
    (v : (SplitSpecies.toQuiver X).V) (s : (SplitSpecies.toQuiver X).VertexOrbit) :
    (SplitSpecies.toQuiver X).vertexClass v = s ↔ v.1 = counitOnI X s := by
  constructor
  · intro h
    rw [← vertexOrbitProj_eq_counitOnI, ← h]
    rfl
  · intro h
    refine (EtaleSpecies.vertex_fiber_eq_orbit X.obj L X.property).1 ?_
    rw [vertexOrbitProj_eq_counitOnI X s]
    exact h

theorem mem_edgeSet_iff {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L)
    (e : (SplitSpecies.toQuiver X).E) (s t : (SplitSpecies.toQuiver X).VertexOrbit) :
    e ∈ (SplitSpecies.toQuiver X).edgeSet s t
      ↔ e.1.1 = (counitOnI X s, counitOnI X t) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine Prod.ext ?_ ?_
    · exact (vertexClass_eq_iff X _ s).mp h1
    · exact (vertexClass_eq_iff X _ t).mp h2
  · intro h
    exact ⟨(vertexClass_eq_iff X _ s).mpr (congrArg Prod.fst h),
      (vertexClass_eq_iff X _ t).mpr (congrArg Prod.snd h)⟩

open MulAction in
/-- **The per-pair form of `RQ2-2.11`.** The edge orbits of `Γ_K(S)` from the vertex orbit `s` to
the vertex orbit `t` are in bijection with `Specm({}_{ι(s)}M_{ι(t)})`, by sending an orbit to the
maximal ideal of any of its members. Well defined because the `Gal(L/K)`-action does not touch the
index component, and bijective by `RQ2-2.11` restricted to one pair: injective because two edges
over the same maximal ideal differ by a Galois element (`edgeSet_orbit_of_index_eq`, i.e.
`exists_galois_comp_eq` on the residue field), surjective because `edge_fiber_eq_orbit` already
produces an edge over every index.

This is the last combinatorial ingredient of the counit's edge component: with it,
`prod_decomposition` decomposes `{}_iM_j` over exactly the index set `E_{st}` that
`S(Γ_K(S))`'s edge algebra is a product over.

@census none (clause witness for `RQ2-2.13-C4`)
-/
noncomputable def edgeOrbitIndex {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L)
    {s t : (SplitSpecies.toQuiver X).VertexOrbit} :
    (SplitSpecies.toQuiver X).EdgeOrbit s t
      → MaximalSpectrum (X.obj.M (counitOnI X s) (counitOnI X t)) :=
  Quotient.lift
    (fun e : (SplitSpecies.toQuiver X).edgeSet s t =>
      EtaleSpecies.edgeIndexOfMem
        ((mem_edgeSet_iff X ((e : (SplitSpecies.toQuiver X).E)) s t).mp e.2))
    (by
      intro a b hab
      obtain ⟨σ, rfl⟩ := mem_orbit_iff.mp hab
      rfl)

theorem edgeOrbitIndex_mk {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L)
    {s t : (SplitSpecies.toQuiver X).VertexOrbit}
    (e : (SplitSpecies.toQuiver X).edgeSet s t) :
    (⟨(counitOnI X s, counitOnI X t), edgeOrbitIndex X (Quotient.mk _ e)⟩
        : X.obj.edgeIndexSet)
      = ((e : (SplitSpecies.toQuiver X).E)).1 :=
  EtaleSpecies.edgeIndex_mk_edgeIndexOfMem _


open MulAction in
theorem edgeSet_orbit_of_index_eq {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {S : EtaleSpecies.{u} K} (x y : S.edgeSet L)
    (h : x.1 = y.1) : ∃ σ : Gal(L/K), σ • x = y := by
  obtain ⟨c, τ⟩ := x
  obtain ⟨c', τ'⟩ := y
  cases h
  obtain ⟨σ, hσ⟩ := EtaleSpecies.exists_galois_comp_eq L (S.residueField c) τ τ'
  exact ⟨σ, congrArg (Sigma.mk c) hσ⟩

open MulAction in
theorem edgeOrbitIndex_bijective {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L)
    (s t : (SplitSpecies.toQuiver X).VertexOrbit) :
    Function.Bijective (edgeOrbitIndex X (s := s) (t := t)) := by
  constructor
  · refine Quotient.ind fun a => Quotient.ind fun b => ?_
    intro hab
    have hidx : ((a : (SplitSpecies.toQuiver X).E)).1 = ((b : (SplitSpecies.toQuiver X).E)).1 := by
      rw [← edgeOrbitIndex_mk X a, ← edgeOrbitIndex_mk X b, hab]
    obtain ⟨σ, hσ⟩ := edgeSet_orbit_of_index_eq
      (a : (SplitSpecies.toQuiver X).E) (b : (SplitSpecies.toQuiver X).E) hidx
    refine Quotient.sound ⟨σ⁻¹, ?_⟩
    refine Subtype.ext ?_
    show σ⁻¹ • ((b : (SplitSpecies.toQuiver X).E)) = (a : (SplitSpecies.toQuiver X).E)
    rw [← hσ]
    exact inv_smul_smul σ _
  · intro m
    obtain ⟨q, hq⟩ := (EtaleSpecies.edge_fiber_eq_orbit X.obj L X.property).2
      (⟨(counitOnI X s, counitOnI X t), m⟩ : X.obj.edgeIndexSet)
    obtain ⟨e₀, rfl⟩ := Quotient.exists_rep q
    have hidx : e₀.1 = (⟨(counitOnI X s, counitOnI X t), m⟩ : X.obj.edgeIndexSet) := hq
    have hmem : e₀ ∈ (SplitSpecies.toQuiver X).edgeSet s t :=
      (mem_edgeSet_iff X e₀ s t).mpr (congrArg Sigma.fst hidx)
    refine ⟨Quotient.mk _ ⟨e₀, hmem⟩, ?_⟩
    have h1 := edgeOrbitIndex_mk X (⟨e₀, hmem⟩ : (SplitSpecies.toQuiver X).edgeSet s t)
    rw [hidx] at h1
    rw [Sigma.mk.injEq] at h1
    exact eq_of_heq h1.2

/-! ### The counit's edge-algebra component

With `edgeOrbitIndex` matching the index sets and `counitOnEdgeField` matching the factors, the
canonical decomposition of `{}_iM_j` into its residue fields *is* the edge algebra of `S(Γ_K(S))`.
-/

theorem edgeOrbitIndex_edgeRep {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L)
    {s t : (SplitSpecies.toQuiver X).VertexOrbit}
    (ε : (SplitSpecies.toQuiver X).EdgeOrbit s t) :
    (⟨(counitOnI X s, counitOnI X t), edgeOrbitIndex X ε⟩ : X.obj.edgeIndexSet)
      = ((SplitSpecies.toQuiver X).edgeRep ε).1 := by
  conv_lhs => rw [← Quotient.out_eq ε]
  exact edgeOrbitIndex_mk X (Quotient.out ε)

noncomputable def edgeOrbitIndexEquiv {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L)
    (s t : (SplitSpecies.toQuiver X).VertexOrbit) :
    (SplitSpecies.toQuiver X).EdgeOrbit s t
      ≃ MaximalSpectrum (X.obj.M (counitOnI X s) (counitOnI X t)) :=
  Equiv.ofBijective _ (edgeOrbitIndex_bijective X s t)

noncomputable def counitOnM {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L)
    (s t : (SplitSpecies.toQuiver X).VertexOrbit) :
    X.obj.M (counitOnI X s) (counitOnI X t)
      ≃ₐ[K] (SplitSpecies.toQuiver X).edgeAlgebra s t :=
  (X.obj.prodDecompositionEquiv (counitOnI X s) (counitOnI X t)).trans
    (((AlgEquiv.piCongrRight fun m =>
        (EtaleSpecies.residueFieldEquivQuotient X.obj
          ⟨(counitOnI X s, counitOnI X t), m⟩).symm).trans
      ((AlgEquiv.piCongrLeft K
        (fun m => (X.obj.residueField ⟨(counitOnI X s, counitOnI X t), m⟩ : Type u))
        (edgeOrbitIndexEquiv X s t)).symm)).trans
      (AlgEquiv.piCongrRight fun ε =>
        (EtaleSpecies.residueFieldEquivOfEq (edgeOrbitIndex_edgeRep X ε)).trans
          (counitOnEdgeField X ε)))

/-- The `ε`-component of `counitOnM`, unfolded. Definitional — the reindexing `AlgEquiv.piCongrLeft`
computes on the nose — and it is what the compatibility squares are proved against: the `ε`-entry
of the image of `x` is `x mod ε`, carried into `L(e_ε)` by the chosen representative of `ε`.

@census none (helper for clause `RQ2-2.13-C4`)
-/
theorem counitOnM_apply {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L)
    (s t : (SplitSpecies.toQuiver X).VertexOrbit)
    (x : X.obj.M (counitOnI X s) (counitOnI X t))
    (ε : (SplitSpecies.toQuiver X).EdgeOrbit s t) :
    counitOnM X s t x ε
      = counitOnEdgeField X ε (EtaleSpecies.residueFieldEquivOfEq (edgeOrbitIndex_edgeRep X ε)
          (X.obj.residueMap ⟨(counitOnI X s, counitOnI X t), edgeOrbitIndex X ε⟩ x)) := rfl

/-- The same, as an equation in `L`. -/
theorem counitOnM_coe {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L)
    (s t : (SplitSpecies.toQuiver X).VertexOrbit)
    (x : X.obj.M (counitOnI X s) (counitOnI X t))
    (ε : (SplitSpecies.toQuiver X).EdgeOrbit s t) :
    (counitOnM X s t x ε).val
      = ((SplitSpecies.toQuiver X).edgeRep ε).2
          (EtaleSpecies.residueFieldEquivOfEq (edgeOrbitIndex_edgeRep X ε)
            (X.obj.residueMap ⟨(counitOnI X s, counitOnI X t), edgeOrbitIndex X ε⟩ x)) := rfl

open MulAction in
/-- **Clause `RQ2-2.13-C4`, the left compatibility square of the counit.** Unwound, the statement
`ρ_s · v_s = s(e_ε)` — the choice defining `edgeComponentLeft` — *is* the equation
`ρ_s ∘ (v_s)_2 = τ_ε ∘ τ_{ε,left}` between algebra maps out of `L_{ι(s)}`, once `edgeSource_congr`
has put `s(e_ε)` over the index `⟨(ι s, ι t), edgeOrbitIndex ε⟩`. Both sides of the square are that
equation evaluated at `α`.

@census none (clause witness for `RQ2-2.13-C4`)
-/
theorem counit_compat_left {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L)
    (s t : (SplitSpecies.toQuiver X).VertexOrbit) :
    (counitOnM X s t).toAlgHom.comp (X.obj.left (counitOnI X s) (counitOnI X t))
      = ((SplitSpecies.toQuiver X).toSpecies.left s t).comp (counitOnL X s).toAlgHom := by
  refine AlgHom.ext fun α => ?_
  funext ε
  refine Subtype.ext ?_
  have hsrc : (SplitSpecies.toQuiver X).toRQuiver.source ((SplitSpecies.toQuiver X).edgeRep ε)
      = (⟨counitOnI X s,
          ((((SplitSpecies.toQuiver X).edgeRep ε).2).comp
            (EtaleSpecies.residueFieldEquivOfEq (edgeOrbitIndex_edgeRep X ε)).toAlgHom).comp
              (X.obj.structLeft ⟨(counitOnI X s, counitOnI X t), edgeOrbitIndex X ε⟩)⟩
        : X.obj.vertexSet L) :=
    (EtaleSpecies.edgeSource_congr (edgeOrbitIndex_edgeRep X ε)
      ((((SplitSpecies.toQuiver X).edgeRep ε).2))).symm
  have hspec := (mem_orbit_iff.mp
    ((SplitSpecies.toQuiver X).source_edgeRep_mem_orbit ε)).choose_spec
  have hsm : (mem_orbit_iff.mp
        ((SplitSpecies.toQuiver X).source_edgeRep_mem_orbit ε)).choose
      • ((SplitSpecies.toQuiver X).vertexRep s)
      = (⟨((SplitSpecies.toQuiver X).vertexRep s).1,
          (mem_orbit_iff.mp
            ((SplitSpecies.toQuiver X).source_edgeRep_mem_orbit ε)).choose
            • (((SplitSpecies.toQuiver X).vertexRep s).2)⟩ : X.obj.vertexSet L) := rfl
  have h2 := EtaleSpecies.sigma_snd_eq (hsm.symm.trans (hspec.trans hsrc))
  have h2app := congrArg (fun f : X.obj.L (counitOnI X s) →ₐ[K] L => f α) h2
  have hL : ((counitOnM X s t
        (X.obj.left (counitOnI X s) (counitOnI X t) α) ε
          : (SplitSpecies.toQuiver X).edgeOrbitField ε) : L)
      = ((((SplitSpecies.toQuiver X).edgeRep ε).2).comp
          (EtaleSpecies.residueFieldEquivOfEq (edgeOrbitIndex_edgeRep X ε)).toAlgHom).comp
            (X.obj.structLeft ⟨(counitOnI X s, counitOnI X t), edgeOrbitIndex X ε⟩) α :=
    counitOnM_coe X s t _ ε
  have hR : (((SplitSpecies.toQuiver X).edgeComponentLeft ε (counitOnL X s α)
        : (SplitSpecies.toQuiver X).edgeOrbitField ε) : L)
      = (mem_orbit_iff.mp
          ((SplitSpecies.toQuiver X).source_edgeRep_mem_orbit ε)).choose
          ((((SplitSpecies.toQuiver X).vertexRep s).2 α)) := by
    rw [RationalQuiver.edgeComponentLeft_coe]
    rfl
  exact hL.trans (h2app.symm.trans hR.symm)


open MulAction in
/-- The right-hand compatibility square, verbatim with `target`/`structRight`/`edgeComponentRight`.

@census none (clause witness for `RQ2-2.13-C4`)
-/
theorem counit_compat_right {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L)
    (s t : (SplitSpecies.toQuiver X).VertexOrbit) :
    (counitOnM X s t).toAlgHom.comp (X.obj.right (counitOnI X s) (counitOnI X t))
      = ((SplitSpecies.toQuiver X).toSpecies.right s t).comp (counitOnL X t).toAlgHom := by
  refine AlgHom.ext fun α => ?_
  funext ε
  refine Subtype.ext ?_
  have hsrc : (SplitSpecies.toQuiver X).toRQuiver.target ((SplitSpecies.toQuiver X).edgeRep ε)
      = (⟨counitOnI X t,
          ((((SplitSpecies.toQuiver X).edgeRep ε).2).comp
            (EtaleSpecies.residueFieldEquivOfEq (edgeOrbitIndex_edgeRep X ε)).toAlgHom).comp
              (X.obj.structRight ⟨(counitOnI X s, counitOnI X t), edgeOrbitIndex X ε⟩)⟩
        : X.obj.vertexSet L) :=
    (EtaleSpecies.edgeTarget_congr (edgeOrbitIndex_edgeRep X ε)
      ((((SplitSpecies.toQuiver X).edgeRep ε).2))).symm
  have hspec := (mem_orbit_iff.mp
    ((SplitSpecies.toQuiver X).target_edgeRep_mem_orbit ε)).choose_spec
  have hsm : (mem_orbit_iff.mp
        ((SplitSpecies.toQuiver X).target_edgeRep_mem_orbit ε)).choose
      • ((SplitSpecies.toQuiver X).vertexRep t)
      = (⟨((SplitSpecies.toQuiver X).vertexRep t).1,
          (mem_orbit_iff.mp
            ((SplitSpecies.toQuiver X).target_edgeRep_mem_orbit ε)).choose
            • (((SplitSpecies.toQuiver X).vertexRep t).2)⟩ : X.obj.vertexSet L) := rfl
  have h2 := EtaleSpecies.sigma_snd_eq (hsm.symm.trans (hspec.trans hsrc))
  have h2app := congrArg (fun f : X.obj.L (counitOnI X t) →ₐ[K] L => f α) h2
  have hL : ((counitOnM X s t
        (X.obj.right (counitOnI X s) (counitOnI X t) α) ε
          : (SplitSpecies.toQuiver X).edgeOrbitField ε) : L)
      = ((((SplitSpecies.toQuiver X).edgeRep ε).2).comp
          (EtaleSpecies.residueFieldEquivOfEq (edgeOrbitIndex_edgeRep X ε)).toAlgHom).comp
            (X.obj.structRight ⟨(counitOnI X s, counitOnI X t), edgeOrbitIndex X ε⟩) α :=
    counitOnM_coe X s t _ ε
  have hR : (((SplitSpecies.toQuiver X).edgeComponentRight ε (counitOnL X t α)
        : (SplitSpecies.toQuiver X).edgeOrbitField ε) : L)
      = (mem_orbit_iff.mp
          ((SplitSpecies.toQuiver X).target_edgeRep_mem_orbit ε)).choose
          ((((SplitSpecies.toQuiver X).vertexRep t).2 α)) := by
    rw [RationalQuiver.edgeComponentRight_coe]
    rfl
  exact hL.trans (h2app.symm.trans hR.symm)

/-- `counitOnI` is a bijection: it *is* `RQ2-2.10`'s orbit projection. -/
theorem counitOnI_bijective {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L) :
    Function.Bijective (counitOnI X) := by
  have h : counitOnI X = EtaleSpecies.vertexOrbitProj X.obj L :=
    funext fun s => (vertexOrbitProj_eq_counitOnI X s).symm
  rw [h]
  exact EtaleSpecies.vertex_fiber_eq_orbit X.obj L X.property

/-- **Clause `RQ2-2.13-C4`.** The counit `S ⟶ S(Γ_K(S))`, with all three components in hand:
`counitOnI` (a bijection, `RQ2-2.10`), `counitOnL` and `counitOnM` (algebra *equivalences*).

@census none (clause witness for `RQ2-2.13-C4`)
-/
noncomputable def counitHom {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L) :
    X.obj ⟶ (SplitSpecies.toQuiver X).toSpecies where
  onI := counitOnI X
  onL := fun t => (counitOnL X t).toAlgHom
  onM := fun s t => (counitOnM X s t).toAlgHom
  compat_left := counit_compat_left X
  compat_right := counit_compat_right X

/-- **Clause `RQ2-2.13-C4`, second conjunct of `speciesAntiEquivalence`.** The counit
`S ⟶ S(Γ_K(S))` is an **isomorphism** of étale `K`-species, pinned by its index component
`counitOnI`. All three components are bijections — `counitOnI` by `RQ2-2.10`, the other two being
algebra equivalences by construction — so `EtaleSpecies.isIso_of_bijective` applies.

@census none (clause witness for `RQ2-2.13-C4`)
-/
theorem counit_iso {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L) :
    ∃ e : X.obj ≅ (SplitSpecies.toQuiver X).toSpecies,
      EtaleSpecies.Hom.onI e.hom = counitOnI X := by
  haveI : IsIso (counitHom X) :=
    EtaleSpecies.isIso_of_bijective _ (counitOnI_bijective X)
      (fun t => (counitOnL X t).bijective) (fun s t => (counitOnM X s t).bijective)
  exact ⟨asIso (counitHom X), rfl⟩





namespace RationalQuiver

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

open MulAction in
/-- On a split quiver every vertex has full stabilizer, so every `L(v)` is `K` (i.e. `⊥ ⊆ L`).

@census none (helper for clause `RQ2-2.13-C7`)
-/
theorem stabField_of_isSplit_V (Γ : RationalQuiver K L) (hΓ : Γ.IsSplit) (x : Γ.V) :
    stabField K L x = ⊥ := by
  have h : stabilizer Gal(L/K) x = ⊤ := by
    ext σ
    simp only [Subgroup.mem_top, iff_true, mem_stabilizer_iff]
    exact (Γ.isSplit_iff.mp hΓ).1 σ x
  rw [stabField, h]
  exact IsGalois.fixedField_top

open MulAction in
/-- The edge form: on a split quiver every `L(e)` is `K` too.

@census none (helper for clause `RQ2-2.13-C7`)
-/
theorem stabField_of_isSplit_E (Γ : RationalQuiver K L) (hΓ : Γ.IsSplit) (e : Γ.E) :
    stabField K L e = ⊥ := by
  have h : stabilizer Gal(L/K) e = ⊤ := by
    ext σ
    simp only [Subgroup.mem_top, iff_true, mem_stabilizer_iff]
    exact (Γ.isSplit_iff.mp hΓ).2 σ e
  rw [stabField, h]
  exact IsGalois.fixedField_top

/-- **Clause `RQ2-2.13-C7`, first half.** A split quiver has split associated species: if `ρ = 1`
then every stabilizer is all of `Gal(L/K)`, so every `L(v)` and every `L(e)` is `L^{Gal(L/K)} = K`,
and `{}_iM_j` is a product of copies of `K`.

@census none (clause witness for `RQ2-2.13-C7`)
-/
theorem toSpecies_isSplit_of_isSplit (Γ : RationalQuiver K L) (hΓ : Γ.IsSplit) :
    (Γ.toSpecies).IsSplit := by
  constructor
  · intro i
    have hsurj : Function.Surjective (algebraMap K (Γ.vertexOrbitField i)) := by
      intro x
      have hx : (x : L) ∈ (⊥ : IntermediateField K L) := by
        rw [← stabField_of_isSplit_V Γ hΓ (Γ.vertexRep i)]
        exact SetLike.coe_mem x
      obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp hx
      exact ⟨k, Subtype.ext hk⟩
    exact ⟨(algebraMap K ((Γ.toSpecies).L i)).injective, hsurj⟩
  · intro i j
    refine ⟨Γ.EdgeOrbit i j, inferInstance, ⟨?_⟩⟩
    exact AlgEquiv.piCongrRight fun ε =>
      (IntermediateField.equivOfEq (stabField_of_isSplit_E Γ hΓ (Γ.edgeRep ε))).trans
        (IntermediateField.botEquiv K L)

end RationalQuiver

/-! ### Split algebras land in `K` (helpers for `RQ2-2.13-C7`, second half)

The three lemmas below are the arithmetic content of the second half of clause `RQ2-2.13-C7`. They
say: a `K`-algebra map out of a *split* algebra cannot see anything beyond `K`, so `Gal(L/K)` fixes
it. For the vertex algebras `L_i` this is immediate (`algebraMap K (L i)` is onto); for the edge
algebras `{}_iM_j ≅ ∏_ε K` it goes through the idempotents `Pi.single e 1`, which any algebra map
into a **field** must send to `0` or `1`.
-/

/-- An idempotent of a field is `0` or `1`.

@census none (helper for clause `RQ2-2.13-C7`)
-/
theorem idem_eq_zero_or_one {F : Type u} [Field F] {x : F} (h : x * x = x) : x = 0 ∨ x = 1 := by
  have hx : x * (x - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.mp hx with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- If `A ≅ ∏_ε K` as `K`-algebras, every `K`-algebra map `A → F` into a field has image inside
`algebraMap K F '' K`. Proof: `a` is the `K`-combination `∑_e (φ a)_e • φ⁻¹(δ_e)` of the idempotents
`δ_e = Pi.single e 1`, each of which maps to an idempotent of `F`, hence to `0` or `1`.

@census none (helper for clause `RQ2-2.13-C7`)
-/
theorem exists_algebraMap_eq_of_split {K F A : Type u} [Field K] [Field F] [Algebra K F]
    [CommRing A] [Algebra K A] {ε : Type u} [Fintype ε] [DecidableEq ε]
    (φ : A ≃ₐ[K] (ε → K)) (g : A →ₐ[K] F) (a : A) : ∃ k : K, g a = algebraMap K F k := by
  classical
  have hdec : ∑ e : ε, (φ a) e • (Pi.single e (1 : K)) = φ a := by
    funext e'; simp [Finset.sum_apply, Pi.single_apply]
  have ha : a = ∑ e : ε, (φ a) e • φ.symm (Pi.single e (1 : K)) := by
    have := congrArg φ.symm hdec
    simpa [map_sum, map_smul] using this.symm
  have hsq : ∀ e : ε, (Pi.single e (1 : K) : ε → K) * (Pi.single e (1 : K))
      = Pi.single e (1 : K) := by
    intro e; funext e'; by_cases h : e = e' <;> simp [h]
  have hidem : ∀ e : ε, g (φ.symm (Pi.single e (1 : K))) = 0 ∨
      g (φ.symm (Pi.single e (1 : K))) = 1 := by
    intro e
    refine idem_eq_zero_or_one ?_
    rw [← map_mul, ← map_mul, hsq e]
  obtain ⟨c, hc⟩ : ∃ c : ε → K, a = ∑ e : ε, c e • φ.symm (Pi.single e (1 : K)) :=
    ⟨fun e => (φ a) e, ha⟩
  refine ⟨∑ e : ε, if g (φ.symm (Pi.single e (1 : K))) = 1 then c e else 0, ?_⟩
  rw [hc, map_sum, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases hidem e with h | h
  · simp [map_smul, h]
  · simp [h, Algebra.smul_def]

/-- If `algebraMap K A` is onto then `Gal(L/K)` fixes every `K`-embedding `A → L`: such an
embedding is determined by its (forced) values on the image of `K`.

@census none (helper for clause `RQ2-2.13-C7`)
-/
theorem emb_smul_eq_self_of_surjective {K L A : Type u} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [CommRing A] [Algebra K A]
    (hA : Function.Surjective (algebraMap K A)) (τ : A →ₐ[K] L) (σ : Gal(L/K)) : σ • τ = τ := by
  refine AlgHom.ext fun a => ?_
  obtain ⟨k, rfl⟩ := hA a
  simp [AlgHom.commutes]

/-- **Clause `RQ2-2.13-C7`, second half.** A split species has split associated quiver: if every
`L_i = K` and every `{}_iM_j = ∏_ε K`, then every `Hom_K(L_i,L)` and every `Hom_K(L_ε,L)` is a
single point, on which `Gal(L/K)` acts trivially.

@census none (clause witness for `RQ2-2.13-C7`)
-/
theorem SplitSpecies.toQuiver_isSplit_of_isSplit {K L : Type u} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] (X : SplitSpecies K L) (hX : X.obj.IsSplit) :
    (SplitSpecies.toQuiver X).IsSplit := by
  classical
  rw [RationalQuiver.isSplit_iff]
  constructor
  · intro σ v
    show (⟨v.1, σ • v.2⟩ : X.obj.vertexSet L) = v
    rw [emb_smul_eq_self_of_surjective (hX.1 v.1).2 v.2 σ]
    rfl
  · intro σ e
    show (⟨e.1, σ • e.2⟩ : X.obj.edgeSet L) = e
    refine congrArg (Sigma.mk e.1) ?_
    obtain ⟨ε, hfin, ⟨φ⟩⟩ := hX.2 e.1.1.1 e.1.1.2
    letI := Fintype.ofFinite ε
    refine AlgHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := X.obj.residueMap_surjective e.1 x
    obtain ⟨k, hk⟩ := exists_algebraMap_eq_of_split φ ((e.2).comp (X.obj.residueMap e.1)) a
    show σ (e.2 (X.obj.residueMap e.1 a)) = e.2 (X.obj.residueMap e.1 a)
    rw [show e.2 (X.obj.residueMap e.1 a) = ((e.2).comp (X.obj.residueMap e.1)) a from rfl, hk]
    exact (σ : L ≃ₐ[K] L).commutes k

open CategoryTheory in
/-- `S(−)` as a contravariant functor into the species **split by `L`** — the form in which it
composes with `Γ_K(−)`, and hence the form in which `RQ2-2.13`'s two round trips are stated.

@census none (clause witness for `RQ2-2.13-C1`)
-/
noncomputable def toSplitSpeciesFunctor (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] : RationalQuiver K L ⥤ (SplitSpecies K L)ᵒᵖ where
  obj Γ := Opposite.op (RationalQuiver.toSplitSpecies Γ)
  map {Γ Γ'} f := Quiver.Hom.op (⟨RationalQuiver.speciesMap f⟩ :
    RationalQuiver.toSplitSpecies Γ' ⟶ RationalQuiver.toSplitSpecies Γ)
  map_id Γ := by
    apply Quiver.Hom.unop_inj
    show (⟨RationalQuiver.speciesMap (𝟙 Γ)⟩ :
      RationalQuiver.toSplitSpecies Γ ⟶ RationalQuiver.toSplitSpecies Γ) = _
    rw [RationalQuiver.speciesMap_id]
    rfl
  map_comp {Γ Γ' Γ''} f g := by
    apply Quiver.Hom.unop_inj
    exact congrArg
      (fun h => (⟨h⟩ : RationalQuiver.toSplitSpecies Γ'' ⟶ RationalQuiver.toSplitSpecies Γ))
      (RationalQuiver.speciesMap_comp f g)

/-- The split `K`-rational quivers, as an object property. -/
def splitQuiverProp (K L : Type u) [Field K] [Field L] [Algebra K L] :
    CategoryTheory.ObjectProperty (RationalQuiver K L) := fun Γ => Γ.IsSplit

/-- The split étale `K`-species (among those split by `L`), as an object property. -/
def splitSpeciesProp (K L : Type u) [Field K] [Field L] [Algebra K L] :
    CategoryTheory.ObjectProperty (SplitSpecies K L) := fun X => X.obj.IsSplit

/-- The object map of the restriction to split objects. -/
noncomputable def splitRestrictionObj (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] (Γ : (splitQuiverProp K L).FullSubcategory) :
    (splitSpeciesProp K L).FullSubcategory :=
  ⟨RationalQuiver.toSplitSpecies Γ.obj,
    RationalQuiver.toSpecies_isSplit_of_isSplit Γ.obj Γ.property⟩

open CategoryTheory in
/-- **Clause `RQ2-2.13-C6`.** The restriction of `S(−)` to the full subcategories of **split**
objects — well defined by clause `C7` (`toSpecies_isSplit_of_isSplit`). That this restriction is
again an (anti-)equivalence is the last conjunct of `speciesAntiEquivalence`.

@census none (clause witness for `RQ2-2.13-C6`)
-/
noncomputable def splitRestriction (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] :
    (splitQuiverProp K L).FullSubcategory ⥤ ((splitSpeciesProp K L).FullSubcategory)ᵒᵖ where
  obj Γ := Opposite.op (splitRestrictionObj K L Γ)
  map {Γ Γ'} f := Quiver.Hom.op
    (⟨⟨RationalQuiver.speciesMap ((splitQuiverProp K L).ι.map f)⟩⟩ :
      splitRestrictionObj K L Γ' ⟶ splitRestrictionObj K L Γ)
  map_id Γ := by
    apply Quiver.Hom.unop_inj
    show (⟨⟨RationalQuiver.speciesMap ((splitQuiverProp K L).ι.map (𝟙 Γ))⟩⟩ :
      splitRestrictionObj K L Γ ⟶ splitRestrictionObj K L Γ) = _
    rw [show (splitQuiverProp K L).ι.map (𝟙 Γ) = 𝟙 Γ.obj from rfl,
      RationalQuiver.speciesMap_id]
    rfl
  map_comp {Γ Γ' Γ''} f g := by
    apply Quiver.Hom.unop_inj
    exact congrArg
      (fun h => (⟨⟨h⟩⟩ : splitRestrictionObj K L Γ'' ⟶ splitRestrictionObj K L Γ))
      (RationalQuiver.speciesMap_comp ((splitQuiverProp K L).ι.map f)
        ((splitQuiverProp K L).ι.map g))

/-! ### Both split full subcategories are inhabited (verification finding **C-4**, G5)

`RQ2-2.13`'s clauses `C6` and `C7` quantify over the full subcategories of split objects, and
`(splitRestriction K L).IsEquivalence` is vacuously true if either is empty. The two witnesses below
close that: a split quiver (one vertex, no edges, `ρ = 1`) and a split species (stage S3's
`EtaleSpecies.trivial`, whose `IsSplit` S3 proved), each with the membership proof the full
subcategory demands. Neither is a `sorry`.
-/

/-- The trivial one-node species on `K` is split by any finite Galois `L/K`: the minimal polynomial
of an element of `K` is `X - a`, which splits everywhere.

@census none (G5 witness for finding C-4)
-/
theorem EtaleSpecies.trivial_isSplitBy (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] : (EtaleSpecies.trivial K).IsSplitBy L := by
  have hsp : ∀ x : K, (Polynomial.map (algebraMap K L) (minpoly K x)).Splits := by
    intro x
    rw [minpoly.eq_X_sub_C' (A := K) x]
    simp
  exact { splits_L := fun _ x => hsp x, splits_M := fun _ _ x => hsp x }

/-- **G5 witness (finding C-4): the split *species* subcategory is inhabited.**

@census none (G5 witness for finding C-4)
-/
noncomputable def splitSpeciesWitness (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] : (splitSpeciesProp K L).FullSubcategory :=
  ⟨⟨EtaleSpecies.trivial K, EtaleSpecies.trivial_isSplitBy K L⟩, EtaleSpecies.trivial_isSplit K⟩

/-- **G5 witness (finding C-4): the split *quiver* subcategory is inhabited** — the one-vertex,
no-edge quiver with the trivial rational structure. Continuity is vacuous because `L/K` is finite.

@census none (G5 witness for finding C-4)
-/
noncomputable def splitQuiverWitness (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] : (splitQuiverProp K L).FullSubcategory :=
  ⟨{ toRQuiver :=
      { V := PUnit
        E := PEmpty
        source := PEmpty.elim
        target := PEmpty.elim
        finite_V := inferInstance
        finite_E := inferInstance }
     ρ := 1
     smooth_V := IsSmooth.of_discreteTopology _
     smooth_E := IsSmooth.of_discreteTopology _ }, rfl⟩

/-! ## The anti-equivalence (census `RQ2-2.13`) -/

/-! ### Naturality of the counit, index and vertex components (clause `RQ2-2.13-C5`)

The index half is `rfl` once both `counitOnI`s are rewritten as `RQ2-2.10`'s projection: on a class
`⟦w⟧` both sides are `g(w₁)`. The vertex half is the usual descent to `L`, with the group element
supplied by `onV_vertexRep_mem_orbit` and the two sides matched by extracting the second component
of the `Σ`-equality `σ · v_X = Γ_K(h)(v_Y)`.
-/

theorem counitOnI_naturality {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X Y : SplitSpecies K L) (h : X ⟶ Y)
    (u : (SplitSpecies.toQuiver Y).VertexOrbit) :
    counitOnI X (RationalQuiver.orbitMap (SplitSpecies.toQuiverMap h) u)
      = EtaleSpecies.Hom.onI ((EtaleSpecies.splitBy K L).ι.map h) (counitOnI Y u) := by
  rw [← vertexOrbitProj_eq_counitOnI, ← vertexOrbitProj_eq_counitOnI]
  refine Quotient.inductionOn u ?_
  intro w
  rfl

open MulAction in
theorem counitOnL_naturality {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X Y : SplitSpecies K L) (h : X ⟶ Y)
    (u : (SplitSpecies.toQuiver Y).VertexOrbit) :
    HEq ((counitOnL Y u).toAlgHom.comp
        (EtaleSpecies.Hom.onL ((EtaleSpecies.splitBy K L).ι.map h) (counitOnI Y u)))
      ((RationalQuiver.speciesMapOnL (SplitSpecies.toQuiverMap h) u).comp
        (counitOnL X (RationalQuiver.orbitMap (SplitSpecies.toQuiverMap h) u)).toAlgHom) := by
  refine EtaleSpecies.heq_algHom_fam (counitOnI_naturality X Y h u).symm ?_
  intro a a' haa
  have hspec := (mem_orbit_iff.mp
    (RationalQuiver.onV_vertexRep_mem_orbit (SplitSpecies.toQuiverMap h) u)).choose_spec
  have hsig : (⟨((SplitSpecies.toQuiver X).vertexRep
          (RationalQuiver.orbitMap (SplitSpecies.toQuiverMap h) u)).1,
        (mem_orbit_iff.mp (RationalQuiver.onV_vertexRep_mem_orbit
            (SplitSpecies.toQuiverMap h) u)).choose
          • ((SplitSpecies.toQuiver X).vertexRep
            (RationalQuiver.orbitMap (SplitSpecies.toQuiverMap h) u)).2⟩ : X.obj.vertexSet L)
      = ⟨EtaleSpecies.Hom.onI ((EtaleSpecies.splitBy K L).ι.map h)
            (((SplitSpecies.toQuiver Y).vertexRep u).1),
          (((SplitSpecies.toQuiver Y).vertexRep u).2).comp
            (EtaleSpecies.Hom.onL ((EtaleSpecies.splitBy K L).ι.map h)
              (((SplitSpecies.toQuiver Y).vertexRep u).1))⟩ := hspec
  have hheq := EtaleSpecies.sigma_heq_snd hsig
  refine Subtype.ext ?_
  show ((counitOnL Y u (EtaleSpecies.Hom.onL ((EtaleSpecies.splitBy K L).ι.map h)
      (counitOnI Y u) a)).val)
    = ((RationalQuiver.speciesMapOnL (SplitSpecies.toQuiverMap h) u
        (counitOnL X (RationalQuiver.orbitMap (SplitSpecies.toQuiverMap h) u) a')).val)
  rw [counitOnL_coe, RationalQuiver.speciesMapOnL_coe, counitOnL_coe]
  exact (EtaleSpecies.heq_algHom_apply_fam (counitOnI_naturality X Y h u) hheq haa.symm).symm


open MulAction in
theorem counitOnM_naturality {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X Y : SplitSpecies K L) (h : X ⟶ Y)
    (s t : (SplitSpecies.toQuiver Y).VertexOrbit) :
    HEq ((counitOnM Y s t).toAlgHom.comp
        (EtaleSpecies.Hom.onM ((EtaleSpecies.splitBy K L).ι.map h)
          (counitOnI Y s) (counitOnI Y t)))
      ((RationalQuiver.speciesMapOnM (SplitSpecies.toQuiverMap h) s t).comp
        (counitOnM X (RationalQuiver.orbitMap (SplitSpecies.toQuiverMap h) s)
          (RationalQuiver.orbitMap (SplitSpecies.toQuiverMap h) t)).toAlgHom) := by
  refine EtaleSpecies.heq_algHom_fam
    (A := fun p : X.obj.I × X.obj.I => X.obj.M p.1 p.2)
    (show ((EtaleSpecies.Hom.onI ((EtaleSpecies.splitBy K L).ι.map h) (counitOnI Y s),
        EtaleSpecies.Hom.onI ((EtaleSpecies.splitBy K L).ι.map h) (counitOnI Y t))
          : X.obj.I × X.obj.I)
      = (counitOnI X (RationalQuiver.orbitMap (SplitSpecies.toQuiverMap h) s),
         counitOnI X (RationalQuiver.orbitMap (SplitSpecies.toQuiverMap h) t)) from
      Prod.ext (counitOnI_naturality X Y h s).symm (counitOnI_naturality X Y h t).symm) ?_
  intro z z' hzz
  funext ε
  refine Subtype.ext ?_
  exact EtaleSpecies.counit_onM_val_aux ((EtaleSpecies.splitBy K L).ι.map h)
    ((SplitSpecies.toQuiver Y).edgeRep ε)
    ((SplitSpecies.toQuiver X).edgeRep
      (RationalQuiver.edgeOrbitMap (SplitSpecies.toQuiverMap h) ε))
    (mem_orbit_iff.mp (RationalQuiver.onE_edgeRep_mem_orbit
      (SplitSpecies.toQuiverMap h) ε)).choose
    (mem_orbit_iff.mp (RationalQuiver.onE_edgeRep_mem_orbit
      (SplitSpecies.toQuiverMap h) ε)).choose_spec
    (edgeOrbitIndex_edgeRep Y ε)
    (edgeOrbitIndex_edgeRep X (RationalQuiver.edgeOrbitMap (SplitSpecies.toQuiverMap h) ε))
    z z' hzz


theorem counitHom_naturality {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X Y : SplitSpecies K L) (h : X ⟶ Y) :
    ((EtaleSpecies.splitBy K L).ι.map h) ≫ counitHom Y
      = counitHom X ≫ RationalQuiver.speciesMap (SplitSpecies.toQuiverMap h) := by
  refine EtaleSpecies.Hom.ext (funext fun u => (counitOnI_naturality X Y h u).symm) ?_ ?_
  · exact Function.hfunext rfl fun u u' huu => by
      cases eq_of_heq huu; exact counitOnL_naturality X Y h u
  · exact Function.hfunext rfl fun s s' hss => by
      cases eq_of_heq hss
      exact Function.hfunext rfl fun t t' htt => by
        cases eq_of_heq htt; exact counitOnM_naturality X Y h s t


/-! ### Naturality of the unit (clause `RQ2-2.13-C5`)

Both halves are the by-now familiar shape. On vertices, `vertexSet_ext_of_val` reduces the square to
`ρ'_{f v} α = ρ_v (σ_f α)`, and `(ρ_v σ_f) · v'_{φ[v]} = f(v)` because `f` is equivariant — one
`stabField_apply_eq_of_smul_eq`. On edges, `edgeSet_ext_of_emb` does the `Σ`-transport,
`heq_edgeOrbit_mk` identifies `edgeOrbitMap f ⟦e⟧` with `⟦f e⟧` (they are the *same* edge, only
indexed differently), and the same group-element identity finishes.

@census none (clause witness for `RQ2-2.13-C5`)
-/

namespace RationalQuiver

open MulAction

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

theorem unitOnV_naturality (Γ Γ' : RationalQuiver K L) (f : Γ ⟶ Γ') (v : Γ.V) :
    EtaleSpecies.vertexMap
        ((EtaleSpecies.splitBy K L).ι.map
          (⟨speciesMap f⟩ : toSplitSpecies Γ' ⟶ toSplitSpecies Γ)) L (Γ.unitOnV v)
      = Γ'.unitOnV (f.toRQuiverHom.onV v) := by
  refine vertexSet_ext_of_val rfl ?_
  intro a ha hb
  have hL : Γ.unitEmb v (speciesMapOnL f (Γ.vertexClass v) ⟨a, ha⟩)
      = (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep v)).choose
          ((mem_orbit_iff.mp (onV_vertexRep_mem_orbit f (Γ.vertexClass v))).choose a) := by
    rw [Γ.unitEmb_coe, speciesMapOnL_coe]
  have hR : Γ'.unitEmb (f.toRQuiverHom.onV v) ⟨a, hb⟩
      = (mem_orbit_iff.mp (Γ'.mem_orbit_vertexRep (f.toRQuiverHom.onV v))).choose a :=
    Γ'.unitEmb_coe _ _
  have ev := (mem_orbit_iff.mp (Γ.mem_orbit_vertexRep v)).choose_spec
  have ef := (mem_orbit_iff.mp (onV_vertexRep_mem_orbit f (Γ.vertexClass v))).choose_spec
  have efv := (mem_orbit_iff.mp (Γ'.mem_orbit_vertexRep (f.toRQuiverHom.onV v))).choose_spec
  have key : (mem_orbit_iff.mp (Γ'.mem_orbit_vertexRep (f.toRQuiverHom.onV v))).choose
        • Γ'.vertexRep (Γ'.vertexClass (f.toRQuiverHom.onV v))
      = ((mem_orbit_iff.mp (Γ.mem_orbit_vertexRep v)).choose *
          (mem_orbit_iff.mp (onV_vertexRep_mem_orbit f (Γ.vertexClass v))).choose)
        • Γ'.vertexRep (Γ'.vertexClass (f.toRQuiverHom.onV v)) := by
    rw [efv, mul_smul]
    show f.toRQuiverHom.onV v = _
    rw [show Γ'.vertexRep (Γ'.vertexClass (f.toRQuiverHom.onV v))
        = Γ'.vertexRep (orbitMap f (Γ.vertexClass v)) from rfl, ef, ← f.equivariant_V, ev]
  have hstab := stabField_apply_eq_of_smul_eq key ⟨a, hb⟩
  show Γ.unitEmb v (speciesMapOnL f (Γ.vertexClass v) ⟨a, ha⟩)
    = Γ'.unitEmb (f.toRQuiverHom.onV v) ⟨a, hb⟩
  rw [hL, hR, hstab, AlgEquiv.mul_apply]

theorem unitOnE_naturality (Γ Γ' : RationalQuiver K L) (f : Γ ⟶ Γ') (e : Γ.E) :
    EtaleSpecies.edgeMap ((EtaleSpecies.splitBy K L).ι.map
        (⟨speciesMap f⟩ : toSplitSpecies Γ' ⟶ toSplitSpecies Γ)) L (Γ.unitOnE e)
      = Γ'.unitOnE (f.toRQuiverHom.onE e) := by
  have hs : orbitMap f (Γ.vertexClass (Γ.toRQuiver.source e))
      = Γ'.vertexClass (Γ'.toRQuiver.source (f.toRQuiverHom.onE e)) :=
    congrArg Γ'.vertexClass (f.toRQuiverHom.onV_source e)
  have ht : orbitMap f (Γ.vertexClass (Γ.toRQuiver.target e))
      = Γ'.vertexClass (Γ'.toRQuiver.target (f.toRQuiverHom.onE e)) :=
    congrArg Γ'.vertexClass (f.toRQuiverHom.onV_target e)
  refine EtaleSpecies.edgeSet_ext_of_emb (Prod.ext hs ht) ?_
  intro x y hxy
  have hcls : HEq (edgeOrbitMap f (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
        (⟨e, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _)))
      (Quotient.mk (orbitRel Gal(L/K) (Γ'.edgeSet _ _))
        (⟨f.toRQuiverHom.onE e, ⟨rfl, rfl⟩⟩ : Γ'.edgeSet _ _)) :=
    heq_edgeOrbit_mk hs ht (f.toRQuiverHom.onE e) _ _
  have hval := edgeAlgebra_apply_val_congr hs ht hxy hcls
  have hrep := edgeRep_heq_congr hs ht hcls
  have eE := (mem_orbit_iff.mp (Γ.mem_orbit_edgeRep (⟨e, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _))).choose_spec
  have eσ := (mem_orbit_iff.mp (onE_edgeRep_mem_orbit f
    (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
      (⟨e, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _)))).choose_spec
  have eF := (mem_orbit_iff.mp (Γ'.mem_orbit_edgeRep
    (⟨f.toRQuiverHom.onE e, ⟨rfl, rfl⟩⟩ : Γ'.edgeSet _ _))).choose_spec
  have key : (mem_orbit_iff.mp (Γ'.mem_orbit_edgeRep
        (⟨f.toRQuiverHom.onE e, ⟨rfl, rfl⟩⟩ : Γ'.edgeSet _ _))).choose
        • Γ'.edgeRep (Quotient.mk (orbitRel Gal(L/K) (Γ'.edgeSet _ _))
            (⟨f.toRQuiverHom.onE e, ⟨rfl, rfl⟩⟩ : Γ'.edgeSet _ _))
      = ((mem_orbit_iff.mp (Γ.mem_orbit_edgeRep (⟨e, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _))).choose *
          (mem_orbit_iff.mp (onE_edgeRep_mem_orbit f
            (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet _ _))
              (⟨e, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _)))).choose)
        • Γ'.edgeRep (Quotient.mk (orbitRel Gal(L/K) (Γ'.edgeSet _ _))
            (⟨f.toRQuiverHom.onE e, ⟨rfl, rfl⟩⟩ : Γ'.edgeSet _ _)) := by
    rw [eF, mul_smul, ← hrep, eσ, ← f.equivariant_E, eE]
  have hstab := stabField_apply_eq_of_smul_eq key
    (y (Quotient.mk (orbitRel Gal(L/K) (Γ'.edgeSet _ _))
      (⟨f.toRQuiverHom.onE e, ⟨rfl, rfl⟩⟩ : Γ'.edgeSet _ _)))
  show Γ.unitEdgeEmb (⟨e, ⟨rfl, rfl⟩⟩ : Γ.edgeSet _ _) (speciesMapOnM f _ _ x)
    = Γ'.unitEdgeEmb (⟨f.toRQuiverHom.onE e, ⟨rfl, rfl⟩⟩ : Γ'.edgeSet _ _) y
  rw [Γ.unitEdgeEmb_coe, Γ'.unitEdgeEmb_coe, hstab, AlgEquiv.mul_apply, ← hval]
  exact congrArg _ (speciesMapOnEdgeField_coe f _ _)

/-- **Clause `RQ2-2.13-C5`, naturality half** — the fourth conjunct of `speciesAntiEquivalence`.
The unit is natural: `Φ_{Γ'} ∘ f = Γ_K(S(f)) ∘ Φ_Γ`.

@census none (clause witness for `RQ2-2.13-C5`)
-/
theorem unitApp_naturality (Γ Γ' : RationalQuiver K L) (f : Γ ⟶ Γ') :
    Γ.unitApp ≫ (toQuiverFunctor K L).map ((toSplitSpeciesFunctor K L).map f)
      = f ≫ Γ'.unitApp :=
  RationalQuiver.Hom.ext (RQuiver.Hom.ext
    (funext fun v => unitOnV_naturality Γ Γ' f v)
    (funext fun e => unitOnE_naturality Γ Γ' f e))

end RationalQuiver

/-! ### The equivalence itself (clause `RQ2-2.13-C5`) -/

noncomputable def counitIsoSplit {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (X : SplitSpecies K L) :
    X ≅ RationalQuiver.toSplitSpecies (SplitSpecies.toQuiver X) :=
  { hom := ⟨counitHom X⟩
    inv := ⟨EtaleSpecies.homInv (counitHom X) (counitOnI_bijective X)
      (fun t => (counitOnL X t).bijective) (fun s t => (counitOnM X s t).bijective)⟩
    hom_inv_id := by
      apply (EtaleSpecies.splitBy K L).ι.map_injective
      exact EtaleSpecies.homInv_hom_id _ _ _ _
    inv_hom_id := by
      apply (EtaleSpecies.splitBy K L).ι.map_injective
      exact EtaleSpecies.homInv_inv_id _ _ _ _ }

/-- **Clause `RQ2-2.13-C5`, the equivalence.** `S(−)` and `Γ_K(−)` are quasi-inverse: the
equivalence `RationalQuiver K L ≌ (SplitSpecies K L)ᵒᵖ` whose functor is `toSplitSpeciesFunctor`
and whose inverse is `toQuiverFunctor` — both **pinned**, which is what verification finding F-1
asked for. The unit is `unitApp` (an isomorphism by `unitApp_isIso`, natural by
`unitApp_naturality`) and the counit is `counitHom` (ditto by `counit_iso` and
`counitHom_naturality`); `Equivalence.mk` adjusts the unit so that the triangle identity holds.

@census none (clause witness for `RQ2-2.13-C5`)
-/
noncomputable def speciesEquivalencePinned (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] : RationalQuiver K L ≌ (SplitSpecies K L)ᵒᵖ :=
  CategoryTheory.Equivalence.mk (toSplitSpeciesFunctor K L) (toQuiverFunctor K L)
    (NatIso.ofComponents
      (fun Γ => @asIso _ _ _ _ (RationalQuiver.unitApp Γ) (RationalQuiver.unitApp_isIso Γ))
      (fun {Γ Γ'} f => (RationalQuiver.unitApp_naturality Γ Γ' f).symm))
    (NatIso.ofComponents (fun X => (counitIsoSplit X.unop).op)
      (fun {X Y} g => by
        apply Quiver.Hom.unop_inj
        apply (EtaleSpecies.splitBy K L).ι.map_injective
        exact (counitHom_naturality Y.unop X.unop g.unop).symm))


theorem speciesEquivalencePinned_functor_inverse (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L] :
    (speciesEquivalencePinned K L).functor = toSplitSpeciesFunctor K L
      ∧ (speciesEquivalencePinned K L).inverse = toQuiverFunctor K L :=
  ⟨rfl, rfl⟩


/-! ### The split full subcategories (clause `RQ2-2.13-C6`)

`splitRestriction` is an equivalence because the big one is, and because the two split-preservation
theorems (`RQ2-2.13-C7`) say the equivalence carries split objects to split objects in both
directions. Faithfulness and fullness come from the big functor's, transported through the (fully
faithful) inclusions of the two full subcategories; essential surjectivity is the counit again, at
a split object, with `toQuiver_isSplit_of_isSplit` supplying the membership proof.
-/

theorem toSplitSpeciesFunctor_faithful (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] : (toSplitSpeciesFunctor K L).Faithful := by
  have h : (speciesEquivalencePinned K L).functor = toSplitSpeciesFunctor K L := rfl
  rw [← h]; infer_instance

theorem toSplitSpeciesFunctor_full (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] : (toSplitSpeciesFunctor K L).Full := by
  have h : (speciesEquivalencePinned K L).functor = toSplitSpeciesFunctor K L := rfl
  rw [← h]; infer_instance

theorem splitRestriction_faithful (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] : (splitRestriction K L).Faithful := by
  haveI := toSplitSpeciesFunctor_faithful K L
  constructor
  intro Γ Γ' f f' hff
  have h1 := congrArg Quiver.Hom.unop hff
  have h2 : RationalQuiver.speciesMap ((splitQuiverProp K L).ι.map f)
      = RationalQuiver.speciesMap ((splitQuiverProp K L).ι.map f') :=
    congrArg (fun z => (EtaleSpecies.splitBy K L).ι.map ((splitSpeciesProp K L).ι.map z)) h1
  have h3 : (toSplitSpeciesFunctor K L).map ((splitQuiverProp K L).ι.map f)
      = (toSplitSpeciesFunctor K L).map ((splitQuiverProp K L).ι.map f') := by
    apply Quiver.Hom.unop_inj
    exact congrArg
      (fun z => (⟨z⟩ : RationalQuiver.toSplitSpecies Γ'.obj ⟶ RationalQuiver.toSplitSpecies Γ.obj))
      h2
  exact (splitQuiverProp K L).ι.map_injective ((toSplitSpeciesFunctor K L).map_injective h3)


theorem splitRestriction_full (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] : (splitRestriction K L).Full := by
  haveI := toSplitSpeciesFunctor_full K L
  constructor
  intro Γ Γ' ψ
  obtain ⟨f, hf⟩ := (toSplitSpeciesFunctor K L).map_surjective
    (Quiver.Hom.op ((splitSpeciesProp K L).ι.map ψ.unop))
  refine ⟨⟨f⟩, ?_⟩
  apply Quiver.Hom.unop_inj
  exact congrArg
    (fun z => (⟨z⟩ : splitRestrictionObj K L Γ' ⟶ splitRestrictionObj K L Γ))
    (congrArg Quiver.Hom.unop hf)

theorem splitRestriction_essSurj (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] : (splitRestriction K L).EssSurj := by
  constructor
  intro X
  refine ⟨⟨SplitSpecies.toQuiver X.unop.obj,
    SplitSpecies.toQuiver_isSplit_of_isSplit X.unop.obj X.unop.property⟩, ⟨?_⟩⟩
  refine Iso.op ?_
  exact { hom := ⟨(counitIsoSplit X.unop.obj).hom⟩
          inv := ⟨(counitIsoSplit X.unop.obj).inv⟩
          hom_inv_id := congrArg (fun z => (⟨z⟩ : X.unop ⟶ X.unop))
            (counitIsoSplit X.unop.obj).hom_inv_id
          inv_hom_id := congrArg
            (fun z => (⟨z⟩ : splitRestrictionObj K L ⟨SplitSpecies.toQuiver X.unop.obj,
                SplitSpecies.toQuiver_isSplit_of_isSplit X.unop.obj X.unop.property⟩
              ⟶ splitRestrictionObj K L ⟨SplitSpecies.toQuiver X.unop.obj,
                SplitSpecies.toQuiver_isSplit_of_isSplit X.unop.obj X.unop.property⟩))
            (counitIsoSplit X.unop.obj).inv_hom_id }


theorem splitRestriction_isEquivalence (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] : (splitRestriction K L).IsEquivalence where
  faithful := splitRestriction_faithful K L
  full := splitRestriction_full K L
  essSurj := splitRestriction_essSurj K L

open CategoryTheory in
/-- **Theorem** (`thm:KrationalquiveretaleKspeciesantiequivalence`, census `RQ2-2.13`).
`S(−)` and `Γ_K(−)` extend to quasi-inverse **contravariant** functors between the category of
`K`-rational quivers and the category of étale `K`-species, inducing anti-equivalences of the
underlying full subcategories of **split** objects.

The seven conjuncts are the conclusion clauses (`C5` contributes two, the pinned equivalence and
the unit naturality):
`C3` — the canonical map `Γ_K ⟶ Γ_K(S(Γ_K))` (`RationalQuiver.unitApp`, the paper's `(Φ_V, Φ_E)`)
is an isomorphism of `K`-rational quivers;
`C4` — the canonical map `S ⟶ S(Γ_K(S))` is an isomorphism of étale `K`-species, pinned by its
index component `counitOnI` (the map `I(Γ_K(S)) → I(S)` of `RQ2-2.10`);
`C5` — the two functors are **quasi-inverse**: there is an equivalence
`RationalQuiver K L ≌ (SplitSpecies K L)ᵒᵖ` whose functor is `S(−)` **and whose inverse is
`Γ_K(−)`**, both pinned by name, together with the naturality of the unit `unitApp` — so the
theorem is about the paper's *two* functors, not about one of them;
`C7` — a split quiver has split associated species and conversely;
`C6` — the anti-equivalence restricts to the full subcategories of split objects.
Clauses `C1` and `C2` are the two functors themselves, `toSplitSpeciesFunctor` (equivalently
`toSpeciesFunctor`, its composite with the inclusion of the `L`-split species) and
`toQuiverFunctor`; `RationalQuiver.speciesMap` and `SplitSpecies.toQuiverMap` are their actions on
morphisms.

@census    RQ2-2.13
@source    thm:KrationalquiveretaleKspeciesantiequivalence
@clauses   RQ2-2.13-H1, RQ2-2.13-C1, RQ2-2.13-C2, RQ2-2.13-C3, RQ2-2.13-C4, RQ2-2.13-C5,
           RQ2-2.13-C6, RQ2-2.13-C7
@imports   none
@divergence JUSTIFIED_REFORMULATION on clauses `RQ2-2.13-H1` and `RQ2-2.13-C4`. *(Until
2026-10-03 this field also named `RQ-2.13-H2`; see the dated `H2` paragraph below.)*

`H1` — "`L` chosen large enough that all actions are `Gal(L/K)`-actions and all occurring finite
étale algebras split over `L`" is rendered as: the ambient Galois extension `L/K` is **finite**
(`[FiniteDimensional K L]`, the source's own "we may assume that `L/K` is finite and Galois" of
§2.3), and the species side is the full subcategory `SplitSpecies K L` of species **split by `L`**.
The census marks this clause `JUSTIFIED_REFORMULATION` in advance ("the choice of `L` is a proof
device"). Nothing is lost: `S(Γ_K)` is always split by `L` (`toSpecies_isSplitBy`), so the
quiver side is untouched, and every étale `K`-species is split by *some* finite Galois `L`.

`H2` — **retired; amended 2026-10-03** (docstring-only `R-PROC-4` amendment of frozen S4,
coordinator ruling `R-FR-9`, final-release WP-16b, stale item R3). Census r18 **retired** clause
`RQ-2.13-H2` (FA-19). The amended source's functoriality argument no longer invokes the
anti-equivalence between finite continuous `G`-sets and finite commutative étale `K`-algebras. It
constructs the two functors explicitly, which is what the Lean does: `S(f)` from the orbit map
together with the fixed-field inclusions `L(f v) ⊆ L(v)`, and `Γ_K(g)` by precomposition, with
continuity carried by `RationalQuiver`'s `smooth_V`/`smooth_E` and the finiteness of `L/K`. The
proof route is therefore now the source's, not a reformulation of it. (The paragraph this replaces
said the `G`-set anti-equivalence was invoked by the source, does not exist in mathlib at this pin
(`MD-S4-02`) and so was not imported. The mathlib fact is still true, but the source no longer needs
it.) On the v2 line (census `census-v2.0`) the retired clause has no row, so the `@clauses` line
above no longer names it (v2 T0, WP-7, 2026-10-17); on v1 it was cited only because v1's `rqaudit
clauses` required every row of `census/CLAUSES.tsv`, retired rows included, to be cited.

**Corrected under verification finding F-1 (2026-08-30).** `C5` previously read
`(toSplitSpeciesFunctor K L).IsEquivalence`, which says only that `S(−)` is an equivalence for
*some* unnamed inverse; `Γ_K(−)` did not occur in the statement at all, and no naturality statement
for `unitApp` existed. It now takes the shape stage S0 set for `RQ2-1.13`
(`Descent/Galois.lean`'s `galoisDescent`): an `∃ e : … ≌ …` with **both** `e.functor` and
`e.inverse` pinned, plus the unit naturality square. That is the census's own gloss of `C5` ("the
isomorphisms are natural") and it is no longer silent.

`C4` — the isomorphism `S ≅ S(Γ_K(S))` is asserted to exist with its **index component named**
(`counitOnI`), rather than as a fully named morphism. The obstruction is the one stage S3 recorded
for `RQ2-2.34`: the edge component compares `{}_{π(s)}M_{π(t)}` with the edge algebra at a *different*
representative of the same orbit, so the two are equal only propositionally and the map needs a
transport. The G4 repair is a named `counitApp` def, exactly as `baseChangeTransIso` is for
`RQ2-2.34`; the vertex component is already pinned, since `counitOnI` is defined at the chosen
representative so that the corestriction of that representative's embedding type-checks without a
transport. Clause `C3`, the half the source proves first and the half every later section uses, is
**not** reformulated: `unitApp` is a named morphism and the clause is `IsIso` of it.

Proof plan (G4), following the source's own two steps.
*Step 1 (`C3`).* `Φ_V` is a bijection because `v ↦ (α ↦ τα)` has the inverse "send `φ` to `τ v_i`
for any `τ` inducing `φ`", well defined by `stabField_apply_eq_of_smul_eq`; `Φ_E` likewise, using
that `Specm` of the finite product `⊕_ε L(e_ε)` is the set of edge orbits (the projection kernels
are maximal, distinct and exhaust it — the lemma `MD-S3-09` records mathlib as lacking);
compatibility with `s`, `t` is the source's computation `s'(φ_e) = φ_e ∘ τ_ε = (α ↦ σα) = Φ_V(s(e))`.
*Step 2 (`C4`).* `Hom_K(L_i,L)` is a single orbit (`RQ2-2.10`) whose stabilizer has fixed field the
image of the embedding, so `L_i ≅ L'_{ι(i)}`; the edge algebras match by `RQ2-2.11` plus
`prod_decomposition`.
*`C5`.* From `C3` and `C4`: `S(−)` is fully faithful and essentially surjective.
*`C6`/`C7`.* If `ρ = 1` every stabilizer is `Gal(L/K)`, so every field is `L^{Gal(L/K)} = K`;
conversely if every `L_i = K` then every `Hom_K(L_i,L)` is a single point and the action is trivial.
-/
theorem speciesAntiEquivalence (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] :
    (∀ Γ : RationalQuiver K L, IsIso (RationalQuiver.unitApp Γ)) ∧
      (∀ X : SplitSpecies K L, ∃ e : X.obj ≅ (SplitSpecies.toQuiver X).toSpecies,
        EtaleSpecies.Hom.onI e.hom = counitOnI X) ∧
      (∃ e : RationalQuiver K L ≌ (SplitSpecies K L)ᵒᵖ,
        e.functor = toSplitSpeciesFunctor K L ∧ e.inverse = toQuiverFunctor K L) ∧
      (∀ (Γ Γ' : RationalQuiver K L) (f : Γ ⟶ Γ'),
        RationalQuiver.unitApp Γ ≫ (toQuiverFunctor K L).map ((toSplitSpeciesFunctor K L).map f)
          = f ≫ RationalQuiver.unitApp Γ') ∧
      (∀ Γ : RationalQuiver K L, Γ.IsSplit → (Γ.toSpecies).IsSplit) ∧
      (∀ X : SplitSpecies K L, X.obj.IsSplit → (SplitSpecies.toQuiver X).IsSplit) ∧
      (splitRestriction K L).IsEquivalence :=
  ⟨fun Γ => RationalQuiver.unitApp_isIso Γ,
    fun X => counit_iso X,
    ⟨speciesEquivalencePinned K L, rfl, rfl⟩,
    fun Γ Γ' f => RationalQuiver.unitApp_naturality Γ Γ' f,
    fun Γ => RationalQuiver.toSpecies_isSplit_of_isSplit Γ,
    fun X => SplitSpecies.toQuiver_isSplit_of_isSplit X,
    splitRestriction_isEquivalence K L⟩

/-! ## Splitting criteria for base-changed algebras

`speciesBaseChange_obj_iso` compares `S(E' ⊗_K Γ_K(X))` with `RQ2-2.05`'s `X ⊗_K E'`, and the
comparison runs through the counit of `RQ2-2.13` at the base-changed species — which is available
only once that species is known to be **split by `L`**. That is the content of this block: a
finite étale algebra all of whose generators have minimal polynomial split by a normal extension
`L/F` is itself split by `L`, and every algebra occurring in `def:basechangeforspecies` is
generated by images of algebras that `X`'s own `IsSplitBy` already splits.

The rule of thumb the block implements is `stages/S4/DESIGN-NOTES.md` §12's, one level up: *never
transport a splitting statement along a tensor product; state it about the generators and let the
étale decomposition do the work.*
-/

namespace SplitAlg

open scoped TensorProduct

variable {F L : Type u} [Field F] [Field L] [Algebra F L]

/-- The minimal polynomial of an image divides that of the element.

@census none (helper for `RQ2-2.08`)
-/
theorem minpoly_dvd_of_algHom {A B : Type u} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (f : A →ₐ[F] B) (x : A) : minpoly F (f x) ∣ minpoly F x := by
  refine minpoly.dvd F _ ?_
  rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]

/-- "Split by `L`" passes to images along an `F`-algebra map.

@census none (helper for `RQ2-2.08`)
-/
theorem splits_of_algHom {A B : Type u} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
    (f : A →ₐ[F] B) (x : A) (hx : IsIntegral F x)
    (h : (Polynomial.map (algebraMap F L) (minpoly F x)).Splits) :
    (Polynomial.map (algebraMap F L) (minpoly F (f x))).Splits := by
  refine Polynomial.Splits.of_dvd h ?_ (Polynomial.map_dvd _ (minpoly_dvd_of_algHom f x))
  exact Polynomial.map_ne_zero (minpoly.ne_zero hx)

/-- A **field** quotient of an algebra generated by elements whose minimal polynomials split in
`L` embeds into `L`. This is `IntermediateField.nonempty_algHom_of_adjoin_splits`, moved across a
surjection.

@census none (helper for `RQ2-2.08`)
-/
theorem nonempty_algHom_of_gens {A P : Type u} [CommRing A] [Algebra F A] [Field P] [Algebra F P]
    (π : A →ₐ[F] P) (hπ : Function.Surjective π) (s : Set A)
    (hs : Algebra.adjoin F s = ⊤)
    (hsplit : ∀ x ∈ s, IsIntegral F x ∧ (Polynomial.map (algebraMap F L) (minpoly F x)).Splits) :
    Nonempty (P →ₐ[F] L) := by
  refine IntermediateField.nonempty_algHom_of_adjoin_splits (S := π '' s) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨IsIntegral.map π (hsplit x hx).1, splits_of_algHom π x (hsplit x hx).1 (hsplit x hx).2⟩
  · refine IntermediateField.toSubalgebra_injective ?_
    rw [IntermediateField.top_toSubalgebra]
    refine top_le_iff.mp (le_trans ?_ (IntermediateField.algebra_adjoin_le_adjoin F _))
    rw [Algebra.adjoin_image, hs]
    rintro x -
    obtain ⟨y, rfl⟩ := hπ x
    exact ⟨y, trivial, rfl⟩

/-- A field with an `F`-embedding into a **normal** extension `L/F` has all its minimal
polynomials split by `L`.

@census none (helper for `RQ2-2.08`)
-/
theorem splits_of_embedding {P : Type u} [Field P] [Algebra F P] [Normal F L]
    (τ : P →ₐ[F] L) (x : P) :
    (Polynomial.map (algebraMap F L) (minpoly F x)).Splits := by
  rw [← minpoly.algHom_eq τ τ.injective x]
  exact Normal.splits ‹Normal F L› (τ x)

/-- An algebra admitting an injective `F`-algebra map into a finite product of copies of `L` has
all its minimal polynomials split by `L`. The `Species/OfQuiver.lean` lemma `splits_minpoly_pi`,
with `L` itself in place of the intermediate fields.

@census none (helper for `RQ2-2.08`)
-/
theorem splits_of_pi_injective {A : Type u} [CommRing A] [Algebra F A] [Normal F L]
    [FiniteDimensional F L] {ι : Type u} [Finite ι]
    (ψ : A →ₐ[F] (ι → L)) (hψ : Function.Injective ψ) (x : A) :
    (Polynomial.map (algebraMap F L) (minpoly F x)).Splits := by
  haveI := Fintype.ofFinite ι
  rw [← minpoly.algHom_eq ψ hψ x]
  set y : ι → L := ψ x with hy
  have key : (Polynomial.aeval y) (∏ i : ι, minpoly F (y i)) = 0 := by
    funext i
    have hc : (Polynomial.aeval y) (∏ i : ι, minpoly F (y i)) i
        = Polynomial.aeval (y i) (∏ i' : ι, minpoly F (y i')) := by
      simp [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    rw [hc, map_prod, Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval F (y i))]
    rfl
  have hdvd : minpoly F y ∣ ∏ i : ι, minpoly F (y i) := minpoly.dvd F y key
  refine Polynomial.Splits.of_dvd ?_ ?_ (Polynomial.map_dvd _ hdvd)
  · rw [Polynomial.map_prod]
    exact Polynomial.Splits.prod fun i _ => Normal.splits ‹Normal F L› (y i)
  · rw [Polynomial.map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      Polynomial.map_ne_zero (minpoly.ne_zero_of_finite F (y i))

/-- **The splitting criterion.** A finite étale `F`-algebra generated by elements whose minimal
polynomials split in the finite normal extension `L/F` is itself split by `L`: its étale
decomposition presents it as a product of fields, each of which is a quotient of it, hence
generated by the images of the generators, hence embeddable in `L`.

@census none (helper for `RQ2-2.08`)
-/
theorem splits_of_etale_gens {A : Type u} [CommRing A] [Algebra F A] [Algebra.Etale F A]
    [Normal F L] [FiniteDimensional F L]
    (s : Set A) (hs : Algebra.adjoin F s = ⊤)
    (hsplit : ∀ x ∈ s, IsIntegral F x ∧ (Polynomial.map (algebraMap F L) (minpoly F x)).Splits)
    (x : A) : (Polynomial.map (algebraMap F L) (minpoly F x)).Splits := by
  obtain ⟨J, hJ, P, hPf, hPa, e, hPfs⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod F A).mp inferInstance
  have hemb : ∀ k : J, Nonempty (P k →ₐ[F] L) := by
    intro k
    refine nonempty_algHom_of_gens ((Pi.evalAlgHom F P k).comp e.toAlgHom) ?_ s hs hsplit
    intro y
    obtain ⟨z, hz⟩ := Function.surjective_eval (β := P) k y
    exact ⟨e.symm z, by simp [hz]⟩
  have τ : ∀ k : J, P k →ₐ[F] L := fun k => (hemb k).some
  refine splits_of_pi_injective
    (Pi.algHom F (fun _ : J => L) fun k => (τ k).comp ((Pi.evalAlgHom F P k).comp e.toAlgHom))
    ?_ x
  intro a b hab
  have h : ∀ k : J, τ k (e a k) = τ k (e b k) := fun k => congrFun hab k
  have h2 : e a = e b := funext fun k => (τ k).injective (h k)
  exact e.injective h2

/-- The `F`-subalgebra of `A ⊗[R] B` generated by the images of the two factors is everything.

@census none (helper for `RQ2-2.08`)
-/
theorem tensor_subalgebra_eq_top {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] {F : Type u} [CommSemiring F] [Algebra F (A ⊗[R] B)]
    (S : Subalgebra F (A ⊗[R] B))
    (hA : ∀ a : A, (a ⊗ₜ[R] (1 : B)) ∈ S) (hB : ∀ b : B, ((1 : A) ⊗ₜ[R] b) ∈ S) : S = ⊤ := by
  have key : ∀ x : A ⊗[R] B, x ∈ S := by
   intro x
   induction x using TensorProduct.induction_on with
   | zero => exact zero_mem _
   | tmul a b =>
       have h : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
         rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
       rw [h]
       exact mul_mem (hA a) (hB b)
   | add x y hx hy => exact add_mem hx hy
  exact top_le_iff.mp fun x _ => key x

/-- The base change of a split finite étale `K`-algebra along `K → F ⊆ L` is split by `L`
over `F`: `F ⊗_K A` is generated over `F` by the elements `1 ⊗ a`, whose minimal polynomials over
`F` divide those over `K`.

@census none (helper for `RQ2-2.08`)
-/
theorem tensor_splits {K : Type u} [Field K] [Algebra K F] [Algebra K L] [IsScalarTower K F L]
    [Normal F L] [FiniteDimensional F L]
    {A : Type u} [CommRing A] [Algebra K A] [Algebra.Etale K A]
    (hA : ∀ x : A, (Polynomial.map (algebraMap K L) (minpoly K x)).Splits)
    (y : F ⊗[K] A) : (Polynomial.map (algebraMap F L) (minpoly F y)).Splits := by
  haveI : Algebra.Etale F (F ⊗[K] A) := Algebra.Etale.baseChange K A F
  haveI : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
  haveI : Module.Finite F (F ⊗[K] A) := Algebra.FormallyUnramified.finite_of_free F (F ⊗[K] A)
  refine splits_of_etale_gens (Set.range (fun a : A => (1 : F) ⊗ₜ[K] a)) ?_ ?_ y
  · refine tensor_subalgebra_eq_top _ (fun a => ?_) (fun b => Algebra.subset_adjoin ⟨b, rfl⟩)
    exact Subalgebra.algebraMap_mem _ a
  · rintro _ ⟨a, rfl⟩
    have hint : IsIntegral F ((1 : F) ⊗ₜ[K] a) := Algebra.IsIntegral.isIntegral _
    have haint : IsIntegral K a := Algebra.IsIntegral.isIntegral a
    refine ⟨hint, ?_⟩
    have hdvd : minpoly F ((1 : F) ⊗ₜ[K] a) ∣ (minpoly K a).map (algebraMap K F) := by
      refine minpoly.dvd _ _ ?_
      rw [Polynomial.aeval_map_algebraMap]
      have h : ((1 : F) ⊗ₜ[K] a) = Algebra.TensorProduct.includeRight a := rfl
      rw [h, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    have hmap : ((minpoly K a).map (algebraMap K F)).map (algebraMap F L)
        = (minpoly K a).map (algebraMap K L) := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    refine Polynomial.Splits.of_dvd ?_ ?_ (Polynomial.map_dvd _ hdvd)
    · rw [hmap]; exact hA a
    · exact Polynomial.map_ne_zero (Polynomial.map_ne_zero (minpoly.ne_zero haint))

/-- An étale algebra generated by the images of two algebras split by `L` is split by `L`.

@census none (helper for `RQ2-2.08`)
-/
theorem splits_of_two_gens [Normal F L] [FiniteDimensional F L]
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra F A] [Algebra F B] [Algebra F C] [Algebra.Etale F C]
    (f : A →ₐ[F] C) (g : B →ₐ[F] C)
    (hgen : Algebra.adjoin F (Set.range f ∪ Set.range g) = ⊤)
    (hAint : Algebra.IsIntegral F A) (hBint : Algebra.IsIntegral F B)
    (hA : ∀ a : A, (Polynomial.map (algebraMap F L) (minpoly F a)).Splits)
    (hB : ∀ b : B, (Polynomial.map (algebraMap F L) (minpoly F b)).Splits)
    (z : C) : (Polynomial.map (algebraMap F L) (minpoly F z)).Splits := by
  haveI := hAint
  haveI := hBint
  refine splits_of_etale_gens (Set.range f ∪ Set.range g) hgen ?_ z
  rintro y (⟨a, rfl⟩ | ⟨b, rfl⟩)
  · exact ⟨IsIntegral.map f (Algebra.IsIntegral.isIntegral a),
      splits_of_algHom f a (Algebra.IsIntegral.isIntegral a) (hA a)⟩
  · exact ⟨IsIntegral.map g (Algebra.IsIntegral.isIntegral b),
      splits_of_algHom g b (Algebra.IsIntegral.isIntegral b) (hB b)⟩

end SplitAlg

namespace EtaleSpecies

open scoped TensorProduct

section BaseChangeSplit

variable {K : Type u} [Field K] (S : EtaleSpecies.{u} K)
variable {L : Type u} [Field L] [Algebra K L]
variable (F : Type u) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]

/-- The chosen decomposition's projection `L_{π(k)} ⊗_K F ↠ L'_k` is surjective.

@census none (helper for `RQ2-2.08`)
-/
theorem baseChangeProj_surjective (p : S.baseChangeIndex F) :
    Function.Surjective (S.baseChangeProj F p) := by
  intro y
  obtain ⟨z, hz⟩ := Function.surjective_eval (β := fun k => (S.vertexSplitting F p.1).F k) p.2 y
  refine ⟨(S.vertexSplitting F p.1).equiv.symm z, ?_⟩
  show (S.vertexSplitting F p.1).equiv ((S.vertexSplitting F p.1).equiv.symm z) p.2 = y
  rw [AlgEquiv.apply_symm_apply]
  exact hz

/-- Each vertex algebra `L'_k` of the base-changed species is split by `L`: it is a quotient of
`F ⊗_K L_{π(k)}`, which `tensor_splits` splits.

@census none (helper for `RQ2-2.08`)
-/
theorem baseChange_splits_L [Normal F L] [FiniteDimensional F L] (hS : S.IsSplitBy L)
    (p : S.baseChangeIndex F) (x : S.baseChangeField F p) :
    (Polynomial.map (algebraMap F L) (minpoly F x)).Splits := by
  haveI : Module.Finite F (F ⊗[K] S.L p.1) :=
    Algebra.FormallyUnramified.finite_of_free F (F ⊗[K] S.L p.1)
  haveI : Algebra.IsIntegral F (F ⊗[K] S.L p.1) := Algebra.IsIntegral.of_finite F _
  obtain ⟨y, rfl⟩ := S.baseChangeProj_surjective F p x
  exact SplitAlg.splits_of_algHom (S.baseChangeProj F p) y (Algebra.IsIntegral.isIntegral y)
    (SplitAlg.tensor_splits (hS.splits_L p.1) y)

/-- Each edge algebra `{}_kM'_ℓ` of the base-changed species is split by `L`. It is
`L'_k ⊗_{A_i} ((F ⊗_K {}_iM_j) ⊗_{A_j} L'_ℓ)`, so `splits_of_two_gens` applies twice, over the
three algebras `L'_k`, `F ⊗_K {}_iM_j`, `L'_ℓ`, each of which is already known to be split.

@census none (helper for `RQ2-2.08`)
-/
theorem baseChange_splits_M [Normal F L] [FiniteDimensional F L] (hS : S.IsSplitBy L)
    (k l : S.baseChangeIndex F) (x : (S.baseChange F).M k l) :
    (Polynomial.map (algebraMap F L) (minpoly F x)).Splits := by
  letI := S.algRightEdge F (S.fibreMap F k) (S.fibreMap F l)
  letI := S.towerRightEdge F (S.fibreMap F k) (S.fibreMap F l)
  letI := S.algVertexField F l
  letI := S.towerVertexField F l
  letI := S.algLeftEdge F (S.fibreMap F k) (S.fibreMap F l)
  letI := S.towerLeftEdge F (S.fibreMap F k) (S.fibreMap F l)
  letI := S.smulCommEdge F (S.fibreMap F k) (S.fibreMap F l)
  letI := S.algVertexField F k
  letI := S.towerVertexField F k
  letI Inner : Type u := (S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l))
    ⊗[S.vertexAlg F (S.fibreMap F l)] (S.baseChangeField F l)
  haveI hEk : Algebra.Etale F (S.baseChangeField F k) := S.etale_baseChangeField F k
  haveI hEl : Algebra.Etale F (S.baseChangeField F l) := S.etale_baseChangeField F l
  haveI : Algebra.Etale (S.vertexAlg F (S.fibreMap F l)) (S.baseChangeField F l) :=
    Algebra.Etale.of_restrictScalars F _ _
  haveI hEdge : Algebra.Etale F (S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l)) :=
    Algebra.Etale.baseChange K (S.M (S.fibreMap F k) (S.fibreMap F l)) F
  haveI : Algebra.Etale (S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l)) Inner :=
    Algebra.Etale.baseChange _ _ _
  haveI hEInner : Algebra.Etale F Inner :=
    Algebra.Etale.comp F (S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l)) Inner
  haveI : Module.Finite F (S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l)) :=
    Algebra.FormallyUnramified.finite_of_free F _
  haveI : Module.Finite F (S.baseChangeField F l) := Algebra.FormallyUnramified.finite_of_free F _
  haveI : Module.Finite F (S.baseChangeField F k) := Algebra.FormallyUnramified.finite_of_free F _
  haveI : Module.Finite F Inner := Algebra.FormallyUnramified.finite_of_free F _
  have hEdgeSplits : ∀ z : S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l),
      (Polynomial.map (algebraMap F L) (minpoly F z)).Splits :=
    SplitAlg.tensor_splits (hS.splits_M (S.fibreMap F k) (S.fibreMap F l))
  have hInner : ∀ z : Inner, (Polynomial.map (algebraMap F L) (minpoly F z)).Splits := by
    refine SplitAlg.splits_of_two_gens
      (AlgHom.restrictScalars F (Algebra.TensorProduct.includeLeft
        (R := S.vertexAlg F (S.fibreMap F l)) (S := S.vertexAlg F (S.fibreMap F l))
        (A := S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l)) (B := S.baseChangeField F l)))
      (AlgHom.restrictScalars F (Algebra.TensorProduct.includeRight
        (R := S.vertexAlg F (S.fibreMap F l))
        (A := S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l)) (B := S.baseChangeField F l)))
      ?_ (Algebra.IsIntegral.of_finite F _) (Algebra.IsIntegral.of_finite F _)
      hEdgeSplits (S.baseChange_splits_L F hS l)
    exact SplitAlg.tensor_subalgebra_eq_top _ (fun a => Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩))
      (fun b => Algebra.subset_adjoin (Or.inr ⟨b, rfl⟩))
  set fOut : (S.baseChangeField F k) →ₐ[F]
      ((S.baseChangeField F k) ⊗[S.vertexAlg F (S.fibreMap F k)] Inner) :=
    AlgHom.restrictScalars F (Algebra.TensorProduct.includeLeft
      (S := S.vertexAlg F (S.fibreMap F k)))
  set gOut : Inner →ₐ[F]
      ((S.baseChangeField F k) ⊗[S.vertexAlg F (S.fibreMap F k)] Inner) :=
    AlgHom.restrictScalars F Algebra.TensorProduct.includeRight
  have hfOut : ∀ a, fOut a = a ⊗ₜ[S.vertexAlg F (S.fibreMap F k)] (1 : Inner) := fun _ => rfl
  have hgOut : ∀ b, gOut b = (1 : S.baseChangeField F k) ⊗ₜ[S.vertexAlg F (S.fibreMap F k)] b :=
    fun _ => rfl
  haveI hEcar : Algebra.Etale F
      ((S.baseChangeField F k) ⊗[S.vertexAlg F (S.fibreMap F k)] Inner) :=
    S.baseChangeEdge_etale F k l
  show (Polynomial.map (algebraMap F L)
    (minpoly F (x : (S.baseChangeField F k) ⊗[S.vertexAlg F (S.fibreMap F k)] Inner))).Splits
  refine SplitAlg.splits_of_two_gens (A := S.baseChangeField F k) (B := Inner)
    (C := (S.baseChangeField F k) ⊗[S.vertexAlg F (S.fibreMap F k)] Inner) fOut gOut
    ?_ (Algebra.IsIntegral.of_finite F _) (Algebra.IsIntegral.of_finite F _)
    (S.baseChange_splits_L F hS k) hInner x
  exact SplitAlg.tensor_subalgebra_eq_top _
    (fun a => Algebra.subset_adjoin (Or.inl ⟨a, hfOut a⟩))
    (fun b => Algebra.subset_adjoin (Or.inr ⟨b, hgOut b⟩))

/-- **The base change of a species split by `L` is again split by `L`.** This is what makes the
counit of `RQ2-2.13` available at `X ⊗_K E'`, and hence what makes the quiver-side route to
`speciesBaseChange_obj_iso` possible at all.

@census none (helper for `RQ2-2.08`)
-/
theorem baseChange_isSplitBy [IsGalois F L] [FiniteDimensional F L] (hS : S.IsSplitBy L) :
    (S.baseChange F).IsSplitBy L := by
  haveI : Normal F L := IsGalois.to_normal
  exact { galois := inferInstance
          findim := inferInstance
          splits_L := fun p x => S.baseChange_splits_L F hS p x
          splits_M := fun k l x => S.baseChange_splits_M F hS k l x }

end BaseChangeSplit

end EtaleSpecies


/-! ## Uniqueness of a decomposition into fields (`MD-S3-09`)

`RQ2-2.34` compares two *chosen* decompositions of `N' ⊗_K L_i` into products of fields — the direct
one and the one obtained in two steps through `N` — so it needs the lemma
`ledger/MATHLIB-DECISIONS.tsv` `MD-S3-09` records mathlib as lacking: a finite étale algebra's
decomposition into fields is unique up to a canonical bijection of index sets. The form proved here
is the useful one: the index of a summand is determined by the **kernel** of its projection
(`ker_proj_injective`), so any index map matching kernels is automatically a bijection
(`splitting_match`).

`exists_pi_index'`/`exists_pi_factor'` are `Species/ToQuiver.lean`'s `exists_pi_index`/
`exists_pi_factor` with the factors weakened from fields to commutative rings — the proof there
uses only the ring structure, and `RQ2-2.34` needs the weaker form, the intermediate algebras
`N' ⊗_N L'_k` not being fields. They are restated rather than generalised in place because
`Species/ToQuiver.lean` is concurrently owned.
-/

namespace PiSplit

open scoped TensorProduct

variable {N : Type u} [Field N] {ι : Type u} [Finite ι] {F : ι → Type u}
  [∀ e, CommRing (F e)] [∀ e, Algebra N (F e)] {B : Type u} [CommRing B] [IsDomain B] [Algebra N B]

/-- `exists_pi_index` for a finite product of **commutative rings** (the proof of the
`Species/ToQuiver.lean` version for fields uses only the ring structure).

@census none (helper for `RQ2-2.34`)
-/
theorem exists_pi_index' (g : (∀ e, F e) →ₐ[N] B) [DecidableEq ι] :
    ∃ e₀ : ι, g (Pi.single e₀ 1) = 1 ∧ ∀ x y : (∀ e, F e), x e₀ = y e₀ → g x = g y := by
  letI := Fintype.ofFinite ι
  have hsum : ∑ e : ι, (Pi.single e 1 : ∀ e, F e) = 1 := by
    funext e'
    simp [Finset.sum_apply, Pi.single_apply]
  have hg : ∑ e : ι, g (Pi.single e 1) = 1 := by
    rw [← map_sum, hsum, map_one]
  have hex : ∃ e₀ : ι, g (Pi.single e₀ 1) ≠ 0 := by
    by_contra hcon
    have hcon : ∀ e : ι, g (Pi.single e 1) = 0 := by
      intro e
      by_contra he
      exact hcon ⟨e, he⟩
    rw [Finset.sum_congr rfl (fun e _ => hcon e), Finset.sum_const_zero] at hg
    exact zero_ne_one hg
  obtain ⟨e₀, he₀⟩ := hex
  have hidem : g (Pi.single e₀ 1) * g (Pi.single e₀ 1) = g (Pi.single e₀ 1) := by
    rw [← map_mul]
    congr 1
    funext e'
    by_cases hb : e₀ = e'
    · subst hb; simp
    · simp [Pi.single_apply, hb]
  have hone : g (Pi.single e₀ (1 : F e₀)) = 1 := by
    have hx : g (Pi.single e₀ 1) * (g (Pi.single e₀ 1) - 1) = 0 := by
      rw [mul_sub, mul_one, hidem, sub_self]
    rcases mul_eq_zero.mp hx with h0 | h1
    · exact absurd h0 he₀
    · exact sub_eq_zero.mp h1
  refine ⟨e₀, hone, fun x y hxy => ?_⟩
  have hz : (x - y) * Pi.single e₀ 1 = 0 := by
    funext e'
    by_cases hb : e₀ = e'
    · subst hb; simp [hxy]
    · simp [Pi.single_apply, hb, Ne.symm hb]
  have := congrArg g hz
  rw [map_mul, hone, mul_one, map_zero, map_sub, sub_eq_zero] at this
  exact this

/-- `exists_pi_factor` for a finite product of commutative rings.

@census none (helper for `RQ2-2.34`)
-/
theorem exists_pi_factor' (g : (∀ e, F e) →ₐ[N] B) :
    ∃ (e₀ : ι) (ĝ : F e₀ →ₐ[N] B), g = ĝ.comp (Pi.evalAlgHom N F e₀) := by
  classical
  obtain ⟨e₀, hone, hdep⟩ := exists_pi_index' g
  have hsingle : ∀ a b : F e₀, (Pi.single e₀ (a * b) : ∀ e, F e)
      = Pi.single e₀ a * Pi.single e₀ b := by
    intro a b
    funext e'
    by_cases hb : e₀ = e'
    · subst hb; simp
    · simp [Pi.single_apply, hb]
  refine ⟨e₀,
    { toFun := fun a => g (Pi.single e₀ a)
      map_one' := hone
      map_mul' := fun a b => by rw [hsingle, map_mul]
      map_zero' := by rw [Pi.single_zero, map_zero]
      map_add' := fun a b => by rw [Pi.single_add, map_add]
      commutes' := fun k => by
        rw [hdep (Pi.single e₀ (algebraMap N (F e₀) k)) (algebraMap N (∀ e, F e) k) (by simp)]
        exact g.commutes k }, ?_⟩
  refine AlgHom.ext fun x => ?_
  exact (hdep (Pi.single e₀ (x e₀)) x (by simp)).symm


variable {N A : Type u} [Field N] [CommRing A] [Algebra N A]

/-- The projections of a decomposition into fields have pairwise distinct kernels.

@census none (helper for `RQ2-2.34`)
-/
theorem ker_proj_injective {C : Type u} [Finite C] {P : C → Type u} [∀ c, Field (P c)]
    [∀ c, Algebra N (P c)] (e : A ≃ₐ[N] ∀ c, P c) :
    Function.Injective (fun c => RingHom.ker ((Pi.evalAlgHom N P c).comp e.toAlgHom)) := by
  classical
  intro c c' h
  have h' : RingHom.ker ((Pi.evalAlgHom N P c).comp e.toAlgHom)
      = RingHom.ker ((Pi.evalAlgHom N P c').comp e.toAlgHom) := h
  by_contra hne
  have hx : e.symm (Pi.single c 1) ∈ RingHom.ker ((Pi.evalAlgHom N P c').comp e.toAlgHom) := by
    show (e (e.symm (Pi.single c 1))) c' = 0
    rw [AlgEquiv.apply_symm_apply]
    exact Pi.single_eq_of_ne (Ne.symm hne) 1
  rw [← h'] at hx
  have hy : (e (e.symm (Pi.single c 1))) c = 1 := by
    rw [AlgEquiv.apply_symm_apply]
    exact Pi.single_eq_same _ _
  exact one_ne_zero (hy.symm.trans hx)

/-- **Uniqueness of a decomposition into fields.** Given `e : A ≃ₐ[N] ∏_c P_c` with the `P_c`
fields and a second family `q_d : A → Q_d` of maps onto fields with pairwise distinct kernels
realising every kernel of the first, any index map `α : D → C` matching kernels is a bijection.
This is the "splitting-uniqueness lemma mathlib lacks" of `MATHLIB-DECISIONS.tsv` `MD-S3-09`.

@census none (helper for `RQ2-2.34`)
-/
theorem splitting_match {C D : Type u} [Finite C] [Finite D]
    {P : C → Type u} [∀ c, Field (P c)] [∀ c, Algebra N (P c)] (e : A ≃ₐ[N] ∀ c, P c)
    {Q : D → Type u} [∀ d, Field (Q d)] [∀ d, Algebra N (Q d)] (q : ∀ d, A →ₐ[N] Q d)
    (hker : Function.Injective (fun d => RingHom.ker (q d)))
    (hsur : ∀ c, ∃ d, RingHom.ker ((Pi.evalAlgHom N P c).comp e.toAlgHom) = RingHom.ker (q d))
    (α : D → C)
    (hα : ∀ d, RingHom.ker ((Pi.evalAlgHom N P (α d)).comp e.toAlgHom) = RingHom.ker (q d)) :
    Function.Bijective α := by
  constructor
  · intro d₁ d₂ h
    refine hker ?_
    show RingHom.ker (q d₁) = RingHom.ker (q d₂)
    rw [← hα d₁, ← hα d₂, h]
  · intro c
    obtain ⟨d, hd⟩ := hsur c
    refine ⟨d, ?_⟩
    exact (ker_proj_injective e (hd.trans (hα d).symm)).symm


end PiSplit

namespace EtaleSpecies

open scoped TensorProduct

variable {K : Type u} [Field K] (S : EtaleSpecies.{u} K) (N : Type u) [Field N] [Algebra K N]
  (i : S.I) {B : Type u} [Field B] [Algebra N B]

/-- The summand of the chosen splitting of `N ⊗_K L_i` through which a map into a field factors.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def bcFactorIndex (g : S.vertexAlg N i →ₐ[N] B) : (S.vertexSplitting N i).J :=
  (EtaleSpecies.exists_pi_factor (g.comp (S.vertexSplitting N i).equiv.symm.toAlgHom)).choose

/-- The induced map on that summand.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def bcFactorHom (g : S.vertexAlg N i →ₐ[N] B) :
    S.baseChangeField N ⟨i, S.bcFactorIndex N i g⟩ →ₐ[N] B :=
  (EtaleSpecies.exists_pi_factor
    (g.comp (S.vertexSplitting N i).equiv.symm.toAlgHom)).choose_spec.choose

theorem bcFactor_spec (g : S.vertexAlg N i →ₐ[N] B) :
    (S.bcFactorHom N i g).comp (S.baseChangeProj N ⟨i, S.bcFactorIndex N i g⟩) = g := by
  have hspec := (EtaleSpecies.exists_pi_factor
    (g.comp (S.vertexSplitting N i).equiv.symm.toAlgHom)).choose_spec.choose_spec
  refine AlgHom.ext fun x => ?_
  have h1 := AlgHom.ext_iff.mp hspec ((S.vertexSplitting N i).equiv x)
  have e1 : (S.vertexSplitting N i).equiv.symm ((S.vertexSplitting N i).equiv x) = x :=
    (S.vertexSplitting N i).equiv.symm_apply_apply x
  exact h1.symm.trans (congrArg (fun y => g y) e1)

theorem bcFactor_ker (g : S.vertexAlg N i →ₐ[N] B) :
    RingHom.ker (S.baseChangeProj N ⟨i, S.bcFactorIndex N i g⟩) = RingHom.ker g := by
  have hg : ∀ x, g x
      = (S.bcFactorHom N i g) (S.baseChangeProj N ⟨i, S.bcFactorIndex N i g⟩ x) :=
    fun x => (AlgHom.ext_iff.mp (S.bcFactor_spec N i g) x).symm
  ext x
  show (S.baseChangeProj N ⟨i, S.bcFactorIndex N i g⟩) x = 0 ↔ g x = 0
  rw [hg x]
  exact (map_eq_zero_iff _ (S.bcFactorHom N i g).injective).symm

theorem baseChangeProj_ker_inj {k k' : (S.vertexSplitting N i).J}
    (h : RingHom.ker (S.baseChangeProj N (⟨i, k⟩ : S.baseChangeIndex N))
      = RingHom.ker (S.baseChangeProj N (⟨i, k'⟩ : S.baseChangeIndex N))) : k = k' :=
  PiSplit.ker_proj_injective (S.vertexSplitting N i).equiv h


end EtaleSpecies


/-! ## The base-change agreement (`speciesBaseChange_obj_iso`), quiver side

The comparison is again quiver-side, and again one statement made twice. Write `A_i = N ⊗_K L_i`
for the base-changed vertex algebra and `∏_{k ∈ J(i)} L'_k` for its chosen splitting. Then

> `Hom_K(L_i, L) ≃ Hom_N(A_i, L) ≃ ⨆_{k ∈ J(i)} Hom_N(L'_k, L)`,

the first bijection being `AlgHom.liftEquiv` and the second the fact that a map from a finite
product of fields into a field factors through exactly one projection (`exists_pi_factor`,
`Species/ToQuiver.lean`). The edge side is the same statement for `{}_iM_j` in place of `L_i`,
once the edge algebra `{}_kM'_ℓ` is known to be generated by the images of `L'_k`, `N ⊗_K {}_iM_j`
and `L'_ℓ` — which is what `edgeMid`, `left_baseChangeProj`, `right_baseChangeProj`,
`baseChangeEdge_hom_ext` and `edgeLift` supply.

`edgeLift` is the universal property of `{}_kM'_ℓ` in the form the surjectivity proof needs: a map
out of `N ⊗_K {}_iM_j` plus compatible maps out of the two vertex fields. It is where the two
"middle" base rings `A_i`, `A_j` become algebra structures on the *target* field, and the §12
discipline applies once more — every index is a variable and the transports live inside one
definition.
-/

namespace EtaleSpecies

section BC
variable {K : Type u} [Field K] (S : EtaleSpecies.{u} K) (N : Type u) [Field N] [Algebra K N]

/-- The middle structure map `N ⊗_K {}_iM_j → {}_kM'_ℓ` of the base-changed edge algebra.

@census none (helper for `RQ2-2.08`)
-/
noncomputable def edgeMid (k l : S.baseChangeIndex N) :
    S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l) →ₐ[N] (S.baseChange N).M k l :=
  letI := S.algRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.towerVertexField N l
  letI := S.algLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.smulCommEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N k
  letI := S.towerVertexField N k
  letI Inner : Type u := (S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))
    ⊗[S.vertexAlg N (S.fibreMap N l)] (S.baseChangeField N l)
  (AlgHom.restrictScalars N
      (Algebra.TensorProduct.includeRight
        (R := S.vertexAlg N (S.fibreMap N k)) (A := S.baseChangeField N k) (B := Inner))).comp
    (AlgHom.restrictScalars N
      (Algebra.TensorProduct.includeLeft
        (R := S.vertexAlg N (S.fibreMap N l)) (S := S.vertexAlg N (S.fibreMap N l))
        (A := S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l)) (B := S.baseChangeField N l)))


theorem left_baseChangeProj (k l : S.baseChangeIndex N)
    (a : S.vertexAlg N (S.fibreMap N k)) :
    (S.baseChange N).left k l (S.baseChangeProj N k a)
      = S.edgeMid N k l (S.edgeHomLeft N (S.fibreMap N k) (S.fibreMap N l) a) := by
  letI := S.algRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.towerVertexField N l
  letI := S.algLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.smulCommEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N k
  letI := S.towerVertexField N k
  letI Inner : Type u := (S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))
    ⊗[S.vertexAlg N (S.fibreMap N l)] (S.baseChangeField N l)
  show S.baseChangeProj N k a ⊗ₜ[S.vertexAlg N (S.fibreMap N k)] (1 : Inner)
      = (1 : S.baseChangeField N k) ⊗ₜ[S.vertexAlg N (S.fibreMap N k)]
        ((S.edgeHomLeft N (S.fibreMap N k) (S.fibreMap N l) a)
          ⊗ₜ[S.vertexAlg N (S.fibreMap N l)] (1 : S.baseChangeField N l))
  have h1 : S.baseChangeProj N k a = a • (1 : S.baseChangeField N k) := by
    rw [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]; rfl
  have h2 : a • (1 : Inner)
      = (S.edgeHomLeft N (S.fibreMap N k) (S.fibreMap N l) a)
        ⊗ₜ[S.vertexAlg N (S.fibreMap N l)] (1 : S.baseChangeField N l) := by
    show a • ((1 : S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))
      ⊗ₜ[S.vertexAlg N (S.fibreMap N l)] (1 : S.baseChangeField N l)) = _
    rw [TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]; rfl
  rw [h1, TensorProduct.smul_tmul, h2]

theorem right_baseChangeProj (k l : S.baseChangeIndex N)
    (b : S.vertexAlg N (S.fibreMap N l)) :
    (S.baseChange N).right k l (S.baseChangeProj N l b)
      = S.edgeMid N k l (S.edgeHomRight N (S.fibreMap N k) (S.fibreMap N l) b) := by
  letI := S.algRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.towerVertexField N l
  letI := S.algLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.smulCommEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N k
  letI := S.towerVertexField N k
  show (1 : S.baseChangeField N k) ⊗ₜ[S.vertexAlg N (S.fibreMap N k)]
      ((1 : S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))
        ⊗ₜ[S.vertexAlg N (S.fibreMap N l)] (S.baseChangeProj N l b))
    = (1 : S.baseChangeField N k) ⊗ₜ[S.vertexAlg N (S.fibreMap N k)]
      ((S.edgeHomRight N (S.fibreMap N k) (S.fibreMap N l) b)
        ⊗ₜ[S.vertexAlg N (S.fibreMap N l)] (1 : S.baseChangeField N l))
  have h1 : S.baseChangeProj N l b = b • (1 : S.baseChangeField N l) := by
    rw [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]; rfl
  have h2 : b • (1 : S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))
      = S.edgeHomRight N (S.fibreMap N k) (S.fibreMap N l) b := by
    rw [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]; rfl
  rw [h1, ← TensorProduct.smul_tmul, h2]

/-- Two `N`-algebra maps out of the base-changed edge algebra agree as soon as they agree on the
images of the three structure maps `left`, `edgeMid`, `right`.

@census none (helper for `RQ2-2.08`)
-/
theorem baseChangeEdge_hom_ext (k l : S.baseChangeIndex N) {C : Type u} [CommRing C] [Algebra N C]
    (Θ Θ' : (S.baseChange N).M k l →ₐ[N] C)
    (hL : ∀ a, Θ ((S.baseChange N).left k l a) = Θ' ((S.baseChange N).left k l a))
    (hM : ∀ z, Θ (S.edgeMid N k l z) = Θ' (S.edgeMid N k l z))
    (hR : ∀ b, Θ ((S.baseChange N).right k l b) = Θ' ((S.baseChange N).right k l b)) :
    Θ = Θ' := by
  letI := S.algRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.towerVertexField N l
  letI := S.algLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.smulCommEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N k
  letI := S.towerVertexField N k
  letI Inner : Type u := (S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))
    ⊗[S.vertexAlg N (S.fibreMap N l)] (S.baseChangeField N l)
  have htop : AlgHom.equalizer Θ Θ' = ⊤ := by
    refine SplitAlg.tensor_subalgebra_eq_top _ (fun a => ?_) (fun z => ?_)
    · exact hL a
    · show ((1 : S.baseChangeField N k) ⊗ₜ[S.vertexAlg N (S.fibreMap N k)] z)
        ∈ AlgHom.equalizer Θ Θ'
      induction z using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
      | tmul m n =>
          have hprod : ((1 : S.baseChangeField N k) ⊗ₜ[S.vertexAlg N (S.fibreMap N k)]
              (m ⊗ₜ[S.vertexAlg N (S.fibreMap N l)] n))
              = S.edgeMid N k l m * (S.baseChange N).right k l n := by
            show _ = ((1 : S.baseChangeField N k) ⊗ₜ[S.vertexAlg N (S.fibreMap N k)]
                (m ⊗ₜ[S.vertexAlg N (S.fibreMap N l)] (1 : S.baseChangeField N l)))
              * ((1 : S.baseChangeField N k) ⊗ₜ[S.vertexAlg N (S.fibreMap N k)]
                ((1 : S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))
                  ⊗ₜ[S.vertexAlg N (S.fibreMap N l)] n))
            simp [Algebra.TensorProduct.tmul_mul_tmul]
          rw [hprod]
          exact mul_mem (hM m) (hR n)
      | add z z' hz hz' =>
          rw [TensorProduct.tmul_add]
          exact add_mem hz hz'
  refine AlgHom.ext fun x => ?_
  have hx : x ∈ AlgHom.equalizer Θ Θ' := by rw [htop]; exact Algebra.mem_top
  exact hx


/-- Change the base of an algebra map, given the compatibility on the new base.

@census none (helper for `RQ2-2.08`)
-/
def upgradeBase {R A C : Type u} [CommSemiring R] [Semiring A] [Semiring C]
    [Algebra R A] [Algebra R C] (f : A →+* C)
    (h : ∀ r : R, f (algebraMap R A r) = algebraMap R C r) : A →ₐ[R] C :=
  { f with commutes' := h }

variable {S N}

/-- The universal property of the base-changed edge algebra, in the form the comparison needs:
a map out of `N ⊗_K {}_iM_j` together with compatible maps out of the two vertex fields extends
to `{}_kM'_ℓ`.

@census none (helper for `RQ2-2.08`)
-/
noncomputable def edgeLift (k l : S.baseChangeIndex N) {C : Type u} [CommRing C] [Algebra N C]
    (g : S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l) →ₐ[N] C)
    (φk : S.baseChangeField N k →ₐ[N] C) (φl : S.baseChangeField N l →ₐ[N] C)
    (hk : ∀ a, φk (S.baseChangeProj N k a)
      = g (S.edgeHomLeft N (S.fibreMap N k) (S.fibreMap N l) a))
    (hl : ∀ b, φl (S.baseChangeProj N l b)
      = g (S.edgeHomRight N (S.fibreMap N k) (S.fibreMap N l) b)) :
    (S.baseChange N).M k l →ₐ[N] C :=
  letI := S.algRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.towerVertexField N l
  letI := S.algLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.smulCommEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N k
  letI := S.towerVertexField N k
  letI algLC : Algebra (S.vertexAlg N (S.fibreMap N k)) C :=
    (g.comp (S.edgeHomLeft N (S.fibreMap N k) (S.fibreMap N l))).toRingHom.toAlgebra
  letI algRC : Algebra (S.vertexAlg N (S.fibreMap N l)) C :=
    (g.comp (S.edgeHomRight N (S.fibreMap N k) (S.fibreMap N l))).toRingHom.toAlgebra
  letI towLC : IsScalarTower N (S.vertexAlg N (S.fibreMap N k)) C :=
    IsScalarTower.of_algebraMap_eq' (by ext n; simp [RingHom.algebraMap_toAlgebra])
  letI towRC : IsScalarTower N (S.vertexAlg N (S.fibreMap N l)) C :=
    IsScalarTower.of_algebraMap_eq' (by ext n; simp [RingHom.algebraMap_toAlgebra])
  letI Inner : Type u := (S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))
    ⊗[S.vertexAlg N (S.fibreMap N l)] (S.baseChangeField N l)
  let gR : S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l) →ₐ[S.vertexAlg N (S.fibreMap N l)] C :=
    upgradeBase g.toRingHom (fun r => rfl)
  let φlR : S.baseChangeField N l →ₐ[S.vertexAlg N (S.fibreMap N l)] C :=
    upgradeBase φl.toRingHom (fun r => hl r)
  let Ψ' : Inner →ₐ[S.vertexAlg N (S.fibreMap N l)] C :=
    Algebra.TensorProduct.lift gR φlR (fun _ _ => Commute.all _ _)
  let Ψ : Inner →ₐ[S.vertexAlg N (S.fibreMap N k)] C :=
    upgradeBase Ψ'.toRingHom (fun r => by
      show Ψ' ((S.edgeHomLeft N (S.fibreMap N k) (S.fibreMap N l) r)
        ⊗ₜ[S.vertexAlg N (S.fibreMap N l)] (1 : S.baseChangeField N l)) = _
      rw [Algebra.TensorProduct.lift_tmul]
      show g _ * φl 1 = _
      rw [map_one, mul_one]
      rfl)
  let φkL : S.baseChangeField N k →ₐ[S.vertexAlg N (S.fibreMap N k)] C :=
    upgradeBase φk.toRingHom (fun r => hk r)
  (show ((S.baseChangeField N k) ⊗[S.vertexAlg N (S.fibreMap N k)] Inner) →ₐ[N] C from
    AlgHom.restrictScalars N (Algebra.TensorProduct.lift φkL Ψ (fun _ _ => Commute.all _ _)))

theorem edgeLift_edgeMid (k l : S.baseChangeIndex N) {C : Type u} [CommRing C] [Algebra N C]
    (g : S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l) →ₐ[N] C)
    (φk : S.baseChangeField N k →ₐ[N] C) (φl : S.baseChangeField N l →ₐ[N] C)
    (hk : ∀ a, φk (S.baseChangeProj N k a)
      = g (S.edgeHomLeft N (S.fibreMap N k) (S.fibreMap N l) a))
    (hl : ∀ b, φl (S.baseChangeProj N l b)
      = g (S.edgeHomRight N (S.fibreMap N k) (S.fibreMap N l) b))
    (z : S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l)) :
    edgeLift k l g φk φl hk hl (S.edgeMid N k l z) = g z := by
  show φk 1 * (g z * φl 1) = g z
  rw [map_one, map_one, mul_one, one_mul]

/-- `edgeLift` restricted along the left structure map is `φk`.

@census none (helper for `RQ2-2.08`, `RQ2-2.34`)
-/
theorem edgeLift_left (k l : S.baseChangeIndex N) {C : Type u} [CommRing C] [Algebra N C]
    (g : S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l) →ₐ[N] C)
    (φk : S.baseChangeField N k →ₐ[N] C) (φl : S.baseChangeField N l →ₐ[N] C)
    (hk : ∀ a, φk (S.baseChangeProj N k a)
      = g (S.edgeHomLeft N (S.fibreMap N k) (S.fibreMap N l) a))
    (hl : ∀ b, φl (S.baseChangeProj N l b)
      = g (S.edgeHomRight N (S.fibreMap N k) (S.fibreMap N l) b))
    (a : S.baseChangeField N k) :
    edgeLift k l g φk φl hk hl ((S.baseChange N).left k l a) = φk a := by
  show φk a * (g 1 * φl 1) = φk a
  rw [map_one, map_one, mul_one, mul_one]

/-- `edgeLift` restricted along the right structure map is `φl`.

@census none (helper for `RQ2-2.08`, `RQ2-2.34`)
-/
theorem edgeLift_right (k l : S.baseChangeIndex N) {C : Type u} [CommRing C] [Algebra N C]
    (g : S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l) →ₐ[N] C)
    (φk : S.baseChangeField N k →ₐ[N] C) (φl : S.baseChangeField N l →ₐ[N] C)
    (hk : ∀ a, φk (S.baseChangeProj N k a)
      = g (S.edgeHomLeft N (S.fibreMap N k) (S.fibreMap N l) a))
    (hl : ∀ b, φl (S.baseChangeProj N l b)
      = g (S.edgeHomRight N (S.fibreMap N k) (S.fibreMap N l) b))
    (b : S.baseChangeField N l) :
    edgeLift k l g φk φl hk hl ((S.baseChange N).right k l b) = φl b := by
  show φk 1 * (g 1 * φl b) = φl b
  rw [map_one, map_one, one_mul, one_mul]

end BC

section Compare

variable {K L N : Type u} [Field K] [Field L] [Field N] [Algebra K L] [Algebra K N] [Algebra N L]
  [IsScalarTower K N L] {S : EtaleSpecies.{u} K}

/-- The `K`-embedding `L_i → L` attached to an `N`-embedding of a base-changed vertex field.

@census none (helper for `RQ2-2.08`)
-/
noncomputable def bcVertexEmb (p : S.baseChangeIndex N) (τ : S.baseChangeField N p →ₐ[N] L) :
    S.L p.1 →ₐ[K] L :=
  (AlgHom.liftEquiv K N (S.L p.1) L).symm (τ.comp (S.baseChangeProj N p))

/-- The vertex comparison `V(Γ_N(S ⊗_K N)) → V(N ⊗_K Γ_K(S))`.

@census none (helper for `RQ2-2.08`)
-/
noncomputable def bcToVertex (S : EtaleSpecies.{u} K) (N : Type u) [Field N] [Algebra K N]
    [Algebra N L] [IsScalarTower K N L] : (S.baseChange N).vertexSet L → S.vertexSet L :=
  fun v => ⟨v.1.1, bcVertexEmb v.1 v.2⟩

/-- The `N`-algebra map `N ⊗_K {}_iM_j → L` attached to a base-changed edge.

@census none (helper for `RQ2-2.08`)
-/
noncomputable def bcEdgeG (c : (S.baseChange N).edgeIndexSet)
    (ψ : (S.baseChange N).residueField c →ₐ[N] L) :
    S.edgeAlg N c.1.1.1 c.1.2.1 →ₐ[N] L :=
  (ψ.comp ((S.baseChange N).residueMap c)).comp (S.edgeMid N c.1.1 c.1.2)

/-- Its left factor through the base-changed source vertex field.

@census none (helper for `RQ2-2.08`)
-/
noncomputable def bcEdgeLeft (c : (S.baseChange N).edgeIndexSet)
    (ψ : (S.baseChange N).residueField c →ₐ[N] L) : S.baseChangeField N c.1.1 →ₐ[N] L :=
  (ψ.comp ((S.baseChange N).residueMap c)).comp ((S.baseChange N).left c.1.1 c.1.2)

/-- Its right factor through the base-changed target vertex field.

@census none (helper for `RQ2-2.08`)
-/
noncomputable def bcEdgeRight (c : (S.baseChange N).edgeIndexSet)
    (ψ : (S.baseChange N).residueField c →ₐ[N] L) : S.baseChangeField N c.1.2 →ₐ[N] L :=
  (ψ.comp ((S.baseChange N).residueMap c)).comp ((S.baseChange N).right c.1.1 c.1.2)

theorem bcEdgeLeft_eval (c : (S.baseChange N).edgeIndexSet)
    (ψ : (S.baseChange N).residueField c →ₐ[N] L)
    (y : ∀ m, (S.vertexSplitting N c.1.1.1).F m) :
    bcEdgeLeft c ψ (y c.1.1.2)
      = bcEdgeG c ψ (S.edgeHomLeft N c.1.1.1 c.1.2.1
          ((S.vertexSplitting N c.1.1.1).equiv.symm y)) := by
  have h := S.left_baseChangeProj N c.1.1 c.1.2 ((S.vertexSplitting N c.1.1.1).equiv.symm y)
  have hy : S.baseChangeProj N c.1.1 ((S.vertexSplitting N c.1.1.1).equiv.symm y) = y c.1.1.2 := by
    show (S.vertexSplitting N c.1.1.1).equiv
      ((S.vertexSplitting N c.1.1.1).equiv.symm y) c.1.1.2 = y c.1.1.2
    rw [AlgEquiv.apply_symm_apply]
  show (ψ.comp ((S.baseChange N).residueMap c)) (((S.baseChange N).left c.1.1 c.1.2) (y c.1.1.2))
    = (ψ.comp ((S.baseChange N).residueMap c)) _
  rw [← hy, h]
  rfl

theorem bcEdgeRight_eval (c : (S.baseChange N).edgeIndexSet)
    (ψ : (S.baseChange N).residueField c →ₐ[N] L)
    (y : ∀ m, (S.vertexSplitting N c.1.2.1).F m) :
    bcEdgeRight c ψ (y c.1.2.2)
      = bcEdgeG c ψ (S.edgeHomRight N c.1.1.1 c.1.2.1
          ((S.vertexSplitting N c.1.2.1).equiv.symm y)) := by
  have h := S.right_baseChangeProj N c.1.1 c.1.2 ((S.vertexSplitting N c.1.2.1).equiv.symm y)
  have hy : S.baseChangeProj N c.1.2 ((S.vertexSplitting N c.1.2.1).equiv.symm y) = y c.1.2.2 := by
    show (S.vertexSplitting N c.1.2.1).equiv
      ((S.vertexSplitting N c.1.2.1).equiv.symm y) c.1.2.2 = y c.1.2.2
    rw [AlgEquiv.apply_symm_apply]
  show (ψ.comp ((S.baseChange N).residueMap c)) (((S.baseChange N).right c.1.1 c.1.2) (y c.1.2.2))
    = (ψ.comp ((S.baseChange N).residueMap c)) _
  rw [← hy, h]
  rfl

/-- The `K`-algebra map `{}_iM_j → L` attached to an `N`-embedding of a base-changed residue
field.

@census none (helper for `RQ2-2.08`)
-/
noncomputable def bcEdgeHom (c : (S.baseChange N).edgeIndexSet)
    (ψ : (S.baseChange N).residueField c →ₐ[N] L) : S.M c.1.1.1 c.1.2.1 →ₐ[K] L :=
  (AlgHom.liftEquiv K N (S.M c.1.1.1 c.1.2.1) L).symm (bcEdgeG c ψ)

/-- The edge comparison `E(Γ_N(S ⊗_K N)) → E(N ⊗_K Γ_K(S))`.

@census none (helper for `RQ2-2.08`)
-/
noncomputable def bcToEdge (S : EtaleSpecies.{u} K) (N : Type u) [Field N] [Algebra K N]
    [Algebra N L] [IsScalarTower K N L] : (S.baseChange N).edgeSet L → S.edgeSet L :=
  fun e => ⟨⟨(e.1.1.1.1, e.1.1.2.1), kerMaximalSpectrum (bcEdgeHom e.1 e.2)⟩,
    S.kerResidueLift (bcEdgeHom e.1 e.2)⟩

/-- The vertex comparison is a bijection: `Hom_K(L_i,L) ≃ Hom_N(N ⊗_K L_i, L)` by
`AlgHom.liftEquiv`, and a map out of the finite product `∏_{k ∈ J(i)} L'_k` into a field factors
through exactly one projection (`exists_pi_factor`).

@census none (helper for `RQ2-2.08`)
-/
theorem bcToVertex_bijective (S : EtaleSpecies.{u} K) (N : Type u) [Field N] [Algebra K N]
    [Algebra N L] [IsScalarTower K N L] :
    Function.Bijective (bcToVertex (L := L) S N) := by
  classical
  constructor
  · rintro ⟨⟨i, k⟩, τ⟩ ⟨⟨i', k'⟩, τ'⟩ heq
    have hi : i = i' := congrArg Sigma.fst heq
    subst hi
    have hsnd : bcVertexEmb (S := S) (L := L) ⟨i, k⟩ τ = bcVertexEmb (S := S) (L := L) ⟨i, k'⟩ τ' :=
      sigma_snd_eq (A := fun i : S.I => S.L i →ₐ[K] L) (i := i) heq
    have hg : τ.comp (S.baseChangeProj N ⟨i, k⟩) = τ'.comp (S.baseChangeProj N ⟨i, k'⟩) :=
      (AlgHom.liftEquiv K N (S.L i) L).symm.injective hsnd
    have hA : ∀ x : (∀ m, (S.vertexSplitting N i).F m), τ (x k) = τ' (x k') := by
      intro x
      have h := AlgHom.ext_iff.mp hg ((S.vertexSplitting N i).equiv.symm x)
      have e1 : (S.vertexSplitting N i).equiv ((S.vertexSplitting N i).equiv.symm x) = x :=
        (S.vertexSplitting N i).equiv.apply_symm_apply x
      show τ (x k) = τ' (x k')
      rw [← e1]
      exact h
    have hkk : k = k' := by
      by_contra hne
      have h1 := hA (Pi.single k 1)
      rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at h1
      exact one_ne_zero ((map_one τ).symm.trans (h1.trans (map_zero τ')))
    subst hkk
    have hτ : τ = τ' := by
      refine AlgHom.ext fun y => ?_
      have h2 := hA (Pi.single k y)
      rwa [Pi.single_eq_same] at h2
    rw [hτ]
  · rintro ⟨i, φ⟩
    obtain ⟨k, ĝ, hĝ⟩ := EtaleSpecies.exists_pi_factor
      (K := N) (F := (S.vertexSplitting N i).F) (B := L)
      (((AlgHom.liftEquiv K N (S.L i) L) φ).comp (S.vertexSplitting N i).equiv.symm.toAlgHom)
    refine ⟨⟨⟨i, k⟩, ĝ⟩, Sigma.ext rfl (heq_of_eq ?_)⟩
    have hcomp : ĝ.comp (S.baseChangeProj N ⟨i, k⟩) = (AlgHom.liftEquiv K N (S.L i) L) φ := by
      refine AlgHom.ext fun x => ?_
      have h1 := AlgHom.ext_iff.mp hĝ ((S.vertexSplitting N i).equiv x)
      have e1 : (S.vertexSplitting N i).equiv.symm ((S.vertexSplitting N i).equiv x) = x :=
        (S.vertexSplitting N i).equiv.symm_apply_apply x
      exact h1.symm.trans (congrArg (fun y => (AlgHom.liftEquiv K N (S.L i) L) φ y) e1)
    exact (congrArg (fun z => (AlgHom.liftEquiv K N (S.L i) L).symm z) hcomp).trans
      ((AlgHom.liftEquiv K N (S.L i) L).symm_apply_apply φ)

/-- Two base-changed edges over the same index pair with the same associated map on
`N ⊗_K {}_iM_j` are equal: the map determines the maximal ideal (its kernel) and, by
`baseChangeEdge_hom_ext`, the embedding.

@census none (helper for `RQ2-2.08`)
-/
theorem bcEdge_theta_eq (k l : S.baseChangeIndex N)
    {ε ε' : MaximalSpectrum ((S.baseChange N).M k l)}
    (ψ : (S.baseChange N).residueField ⟨(k, l), ε⟩ →ₐ[N] L)
    (ψ' : (S.baseChange N).residueField ⟨(k, l), ε'⟩ →ₐ[N] L)
    (hG : bcEdgeG ⟨(k, l), ε⟩ ψ = bcEdgeG ⟨(k, l), ε'⟩ ψ') :
    (⟨⟨(k, l), ε⟩, ψ⟩ : (S.baseChange N).edgeSet L) = ⟨⟨(k, l), ε'⟩, ψ'⟩ := by
  have hΘ : (ψ.comp ((S.baseChange N).residueMap ⟨(k, l), ε⟩))
      = (ψ'.comp ((S.baseChange N).residueMap ⟨(k, l), ε'⟩)) := by
    refine S.baseChangeEdge_hom_ext N k l _ _ ?_ ?_ ?_
    · intro a
      obtain ⟨x, rfl⟩ := S.baseChangeProj_surjective N k a
      rw [S.left_baseChangeProj N k l x]
      exact AlgHom.ext_iff.mp hG _
    · intro z
      exact AlgHom.ext_iff.mp hG z
    · intro b
      obtain ⟨y, rfl⟩ := S.baseChangeProj_surjective N l b
      rw [S.right_baseChangeProj N k l y]
      exact AlgHom.ext_iff.mp hG _
  have hε : ε = ε' := MaximalSpectrum.ext (by
    rw [← ker_comp_residueMap (S.baseChange N) ⟨(k, l), ε⟩ ψ,
      ← ker_comp_residueMap (S.baseChange N) ⟨(k, l), ε'⟩ ψ', hΘ])
  exact edgeSet_ext_of_val hε (fun x => AlgHom.ext_iff.mp hΘ x)

/-- The edge comparison is injective.

@census none (helper for `RQ2-2.08`)
-/
theorem bcToEdge_injective (S : EtaleSpecies.{u} K) (N : Type u) [Field N] [Algebra K N]
    [Algebra N L] [IsScalarTower K N L] :
    Function.Injective (bcToEdge (L := L) S N) := by
  classical
  rintro ⟨⟨⟨⟨i₁, m₁⟩, ⟨j₁, n₁⟩⟩, ε₁⟩, ψ₁⟩ ⟨⟨⟨⟨i₂, m₂⟩, ⟨j₂, n₂⟩⟩, ε₂⟩, ψ₂⟩ heq
  have hp : ((i₁, j₁) : S.I × S.I) = (i₂, j₂) :=
    congrArg Sigma.fst (congrArg Sigma.fst heq)
  have hi : i₁ = i₂ := congrArg Prod.fst hp
  have hj : j₁ = j₂ := congrArg Prod.snd hp
  subst hi
  subst hj
  have hφ : bcEdgeHom (S := S) (L := L) ⟨(⟨i₁, m₁⟩, ⟨j₁, n₁⟩), ε₁⟩ ψ₁
      = bcEdgeHom ⟨(⟨i₁, m₂⟩, ⟨j₁, n₂⟩), ε₂⟩ ψ₂ :=
    AlgHom.ext fun x => edgeSet_val_of_eq heq HEq.rfl
  have hG : bcEdgeG (S := S) (L := L) ⟨(⟨i₁, m₁⟩, ⟨j₁, n₁⟩), ε₁⟩ ψ₁
      = bcEdgeG ⟨(⟨i₁, m₂⟩, ⟨j₁, n₂⟩), ε₂⟩ ψ₂ :=
    (AlgHom.liftEquiv K N (S.M i₁ j₁) L).symm.injective hφ
  have hm : m₁ = m₂ := by
    by_contra hne
    set y : ∀ m, (S.vertexSplitting N i₁).F m := Pi.single m₁ 1 with hydef
    have h1 := bcEdgeLeft_eval (S := S) (L := L) ⟨(⟨i₁, m₁⟩, ⟨j₁, n₁⟩), ε₁⟩ ψ₁ y
    have h2 := bcEdgeLeft_eval (S := S) (L := L) ⟨(⟨i₁, m₂⟩, ⟨j₁, n₂⟩), ε₂⟩ ψ₂ y
    rw [hG] at h1
    have h3 : bcEdgeLeft (S := S) (L := L) ⟨(⟨i₁, m₁⟩, ⟨j₁, n₁⟩), ε₁⟩ ψ₁ (y m₁)
        = bcEdgeLeft (S := S) (L := L) ⟨(⟨i₁, m₂⟩, ⟨j₁, n₂⟩), ε₂⟩ ψ₂ (y m₂) := h1.trans h2.symm
    have hy1 : y m₁ = 1 := Pi.single_eq_same _ _
    have hy2 : y m₂ = 0 := Pi.single_eq_of_ne (Ne.symm hne) _
    rw [hy1, hy2] at h3
    exact one_ne_zero ((map_one _).symm.trans (h3.trans (map_zero _)))
  have hn : n₁ = n₂ := by
    by_contra hne
    set y : ∀ m, (S.vertexSplitting N j₁).F m := Pi.single n₁ 1 with hydef
    have h1 := bcEdgeRight_eval (S := S) (L := L) ⟨(⟨i₁, m₁⟩, ⟨j₁, n₁⟩), ε₁⟩ ψ₁ y
    have h2 := bcEdgeRight_eval (S := S) (L := L) ⟨(⟨i₁, m₂⟩, ⟨j₁, n₂⟩), ε₂⟩ ψ₂ y
    rw [hG] at h1
    have h3 : bcEdgeRight (S := S) (L := L) ⟨(⟨i₁, m₁⟩, ⟨j₁, n₁⟩), ε₁⟩ ψ₁ (y n₁)
        = bcEdgeRight (S := S) (L := L) ⟨(⟨i₁, m₂⟩, ⟨j₁, n₂⟩), ε₂⟩ ψ₂ (y n₂) := h1.trans h2.symm
    have hy1 : y n₁ = 1 := Pi.single_eq_same _ _
    have hy2 : y n₂ = 0 := Pi.single_eq_of_ne (Ne.symm hne) _
    rw [hy1, hy2] at h3
    exact one_ne_zero ((map_one _).symm.trans (h3.trans (map_zero _)))
  subst hm
  subst hn
  exact bcEdge_theta_eq ⟨i₁, m₁⟩ ⟨j₁, n₁⟩ ψ₁ ψ₂ hG

/-- The edge comparison is surjective: a `K`-algebra map `{}_iM_j → L` extends, by
`AlgHom.liftEquiv`, to `N ⊗_K {}_iM_j`; its two restrictions to the base-changed vertex algebras
factor through unique summands `L'_k`, `L'_ℓ` (`exists_pi_factor`), and `edgeLift` assembles the
three into a map out of `{}_kM'_ℓ`.

@census none (helper for `RQ2-2.08`)
-/
theorem bcToEdge_surjective (S : EtaleSpecies.{u} K) (N : Type u) [Field N] [Algebra K N]
    [Algebra N L] [IsScalarTower K N L] :
    Function.Surjective (bcToEdge (L := L) S N) := by
  rintro ⟨⟨⟨i, j⟩, ε⟩, ψ₀⟩
  set θ : S.M i j →ₐ[K] L := ψ₀.comp (S.residueMap ⟨(i, j), ε⟩) with hθ
  set g : S.edgeAlg N i j →ₐ[N] L := (AlgHom.liftEquiv K N (S.M i j) L) θ with hgdef
  obtain ⟨m, φk, hφk⟩ := EtaleSpecies.exists_pi_factor
    (K := N) (F := (S.vertexSplitting N i).F) (B := L)
    ((g.comp (S.edgeHomLeft N i j)).comp (S.vertexSplitting N i).equiv.symm.toAlgHom)
  obtain ⟨n, φl, hφl⟩ := EtaleSpecies.exists_pi_factor
    (K := N) (F := (S.vertexSplitting N j).F) (B := L)
    ((g.comp (S.edgeHomRight N i j)).comp (S.vertexSplitting N j).equiv.symm.toAlgHom)
  have hk : ∀ a, φk (S.baseChangeProj N (⟨i, m⟩ : S.baseChangeIndex N) a)
      = g (S.edgeHomLeft N i j a) := by
    intro a
    have h := AlgHom.ext_iff.mp hφk ((S.vertexSplitting N i).equiv a)
    have e1 : (S.vertexSplitting N i).equiv.symm ((S.vertexSplitting N i).equiv a) = a :=
      (S.vertexSplitting N i).equiv.symm_apply_apply a
    exact (h.symm.trans (congrArg (fun z => g (S.edgeHomLeft N i j z)) e1))
  have hl : ∀ b, φl (S.baseChangeProj N (⟨j, n⟩ : S.baseChangeIndex N) b)
      = g (S.edgeHomRight N i j b) := by
    intro b
    have h := AlgHom.ext_iff.mp hφl ((S.vertexSplitting N j).equiv b)
    have e1 : (S.vertexSplitting N j).equiv.symm ((S.vertexSplitting N j).equiv b) = b :=
      (S.vertexSplitting N j).equiv.symm_apply_apply b
    exact (h.symm.trans (congrArg (fun z => g (S.edgeHomRight N i j z)) e1))
  set Θ : (S.baseChange N).M ⟨i, m⟩ ⟨j, n⟩ →ₐ[N] L :=
    edgeLift ⟨i, m⟩ ⟨j, n⟩ g φk φl hk hl with hΘ
  refine ⟨⟨⟨(⟨i, m⟩, ⟨j, n⟩), kerMaximalSpectrum Θ⟩, (S.baseChange N).kerResidueLift Θ⟩, ?_⟩
  have hφ' : bcEdgeHom (S := S) (L := L)
      ⟨(⟨i, m⟩, ⟨j, n⟩), kerMaximalSpectrum Θ⟩ ((S.baseChange N).kerResidueLift Θ) = θ := by
    have hgg : bcEdgeG (S := S) (L := L)
        ⟨(⟨i, m⟩, ⟨j, n⟩), kerMaximalSpectrum Θ⟩ ((S.baseChange N).kerResidueLift Θ) = g :=
      AlgHom.ext fun z => edgeLift_edgeMid ⟨i, m⟩ ⟨j, n⟩ g φk φl hk hl z
    show (AlgHom.liftEquiv K N (S.M i j) L).symm _ = θ
    rw [hgg, hgdef]
    exact (AlgHom.liftEquiv K N (S.M i j) L).symm_apply_apply θ
  refine edgeSet_ext_of_emb rfl ?_
  intro x y hxy
  cases hxy
  rw [hφ']
  rfl

/-- The comparison commutes with the source maps.

@census none (helper for `RQ2-2.08`)
-/
theorem bcToVertex_source (S : EtaleSpecies.{u} K) (N : Type u) [Field N] [Algebra K N]
    [Algebra N L] [IsScalarTower K N L] (e : (S.baseChange N).edgeSet L) :
    bcToVertex S N ((S.baseChange N).edgeSource L e) = S.edgeSource L (bcToEdge S N e) := by
  refine Sigma.ext rfl (heq_of_eq (AlgHom.ext fun a => ?_))
  show e.2 ((S.baseChange N).residueMap e.1 ((S.baseChange N).left e.1.1.1 e.1.1.2
      (S.baseChangeProj N e.1.1.1 ((1 : N) ⊗ₜ[K] a)))) = _
  rw [S.left_baseChangeProj N e.1.1.1 e.1.1.2 ((1 : N) ⊗ₜ[K] a)]
  rfl

/-- The comparison commutes with the target maps.

@census none (helper for `RQ2-2.08`)
-/
theorem bcToVertex_target (S : EtaleSpecies.{u} K) (N : Type u) [Field N] [Algebra K N]
    [Algebra N L] [IsScalarTower K N L] (e : (S.baseChange N).edgeSet L) :
    bcToVertex S N ((S.baseChange N).edgeTarget L e) = S.edgeTarget L (bcToEdge S N e) := by
  refine Sigma.ext rfl (heq_of_eq (AlgHom.ext fun a => ?_))
  show e.2 ((S.baseChange N).residueMap e.1 ((S.baseChange N).right e.1.1.1 e.1.1.2
      (S.baseChangeProj N e.1.1.2 ((1 : N) ⊗ₜ[K] a)))) = _
  rw [S.right_baseChangeProj N e.1.1.1 e.1.1.2 ((1 : N) ⊗ₜ[K] a)]
  rfl

end Compare

section QuiverIso

open CategoryTheory

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
variable (S : EtaleSpecies.{u} K) (E' : IntermediateField K L) [FiniteDimensional K E']

theorem bcToVertex_equivariant (σ : Gal(L/(E' : Type u)))
    (v : (S.baseChange (E' : Type u)).vertexSet L) :
    bcToVertex S (E' : Type u) (σ • v)
      = (galRestrict K L E' σ) • bcToVertex S (E' : Type u) v := rfl

theorem bcToEdge_equivariant (σ : Gal(L/(E' : Type u)))
    (e : (S.baseChange (E' : Type u)).edgeSet L) :
    bcToEdge S (E' : Type u) (σ • e)
      = (galRestrict K L E' σ) • bcToEdge S (E' : Type u) e := by
  refine edgeSet_ext_of_val (MaximalSpectrum.ext ?_) (fun x => rfl)
  exact ker_smul_comp (bcEdgeHom e.1 e.2) (galRestrict K L E' σ)

/-- The comparison morphism of `E'`-rational quivers `Γ_{E'}(S ⊗_K E') ⟶ E' ⊗_K Γ_K(S)`.

@census none (helper for `RQ2-2.08`)
-/
noncomputable def bcQuiverHom (hS : S.IsSplitBy L)
    (hY : (S.baseChange (E' : Type u)).IsSplitBy L) :
    (S.baseChange (E' : Type u)).toRationalQuiver L hY ⟶
      (RationalQuiver.baseChange K L E').obj (S.toRationalQuiver L hS) where
  toRQuiverHom :=
    { onV := bcToVertex S (E' : Type u)
      onE := bcToEdge S (E' : Type u)
      onV_source := bcToVertex_source S (E' : Type u)
      onV_target := bcToVertex_target S (E' : Type u) }
  equivariant_V := bcToVertex_equivariant S E'
  equivariant_E := bcToEdge_equivariant S E'

/-- It is an isomorphism.

@census none (helper for `RQ2-2.08`)
-/
theorem bcQuiverHom_isIso (hS : S.IsSplitBy L)
    (hY : (S.baseChange (E' : Type u)).IsSplitBy L) : IsIso (bcQuiverHom S E' hS hY) :=
  RationalQuiver.isIso_of_bijective _ (bcToVertex_bijective S (E' : Type u))
    ⟨bcToEdge_injective S (E' : Type u), bcToEdge_surjective S (E' : Type u)⟩

end QuiverIso

end EtaleSpecies


/-! ## The restriction agreement (`speciesRestriction_obj_iso`), quiver side

`res_{E'/K}` on quivers is the induced set `Gal(L/K) ×_{Gal(L/E')} (−)` and `res_{E'/K}` on species
keeps the carriers and composes the structure maps with `K → E'`. The agreement theorem is
therefore, on the quiver side, one statement made twice — once for `V`, once for `E`:

> `Gal(L/K) ×_{Gal(L/E')} Hom_{E'}(A, L) ≅ Hom_K(A, L)`, `(g, φ) ↦ g ∘ φ`,

for `A` a field over `E'` that `L` splits. Surjectivity is `MD-S4-01` (`exists_galois_comp_eq`);
injectivity is the observation that if `g ∘ φ = g' ∘ φ'` with `φ`, `φ'` both `E'`-linear then
`g'^{-1} g` fixes `E'` pointwise, hence lies in `range (galRestrict) = E'.fixingSubgroup`
(`range_galRestrict`) — which is exactly the relation defining the induced set.

The two `Gal(L/E')`-sets carry separate `MulAction` instances (`vertexSet`, `edgeSet`), so, as
`stages/S4/DESIGN-NOTES.md` §17.1 records for `stabField_vertexSet`/`stabField_edgeSet`, the
statement is written twice rather than once.
-/

namespace RestrictionIso

open EtaleSpecies

section

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
variable {E' : IntermediateField K L} [FiniteDimensional K E']

/-- Two `E'`-embeddings of a field into `L` whose `Gal(L/K)`-translates agree differ by an element
of `Gal(L/E')`, in the shape the induced set `Gal(L/K) ×_{Gal(L/E')} (−)` needs.

@census none (helper for `RQ2-2.08`)
-/
theorem exists_gal_of_eq {A : Type u} [Field A] [Algebra (E' : Type u) A]
    (φ φ' : A →ₐ[(E' : Type u)] L) (g g' : Gal(L/K))
    (hpt : ∀ x : A, g (φ x) = g' (φ' x)) :
    ∃ h : Gal(L/(E' : Type u)), g' = g * (galRestrict K L E' h)⁻¹ ∧ φ' = h • φ := by
  have hfix : (g'⁻¹ * g) ∈ E'.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro a ha
    have h1 : φ (algebraMap (E' : Type u) A ⟨a, ha⟩) = a := by rw [AlgHom.commutes]; rfl
    have h2 : φ' (algebraMap (E' : Type u) A ⟨a, ha⟩) = a := by rw [AlgHom.commutes]; rfl
    have hx := hpt (algebraMap (E' : Type u) A ⟨a, ha⟩)
    rw [h1, h2] at hx
    show g'.symm (g a) = a
    rw [hx]
    exact g'.symm_apply_apply a
  have hmem : (g'⁻¹ * g) ∈ (galRestrict K L E').range := by
    rw [range_galRestrict]; exact hfix
  obtain ⟨h0, hh0⟩ := hmem
  refine ⟨h0, by rw [hh0]; group, ?_⟩
  refine AlgHom.ext fun x => ?_
  show φ' x = h0 (φ x)
  have hg : (galRestrict K L E' h0) (φ x) = g'.symm (g (φ x)) := by rw [hh0]; rfl
  rw [hpt x, g'.symm_apply_apply] at hg
  exact hg.symm

variable {Y : EtaleSpecies.{u} (E' : Type u)}

/-- An `E'`-embedding of a vertex field, read as a `K`-embedding of the *restricted* vertex field.
The carrier is unchanged (`restriction_L`), so only the `commutes'` field has content, and it is
`φ.commutes` at `algebraMap K E' r`.

@census none (helper for `RQ2-2.08`)
-/
noncomputable def restrictVertexEmb (i : Y.I) (φ : Y.L i →ₐ[(E' : Type u)] L) :
    (EtaleSpecies.restriction (K := K) Y).L i →ₐ[K] L where
  toFun := φ
  map_one' := φ.map_one
  map_mul' := φ.map_mul
  map_zero' := φ.map_zero
  map_add' := φ.map_add
  commutes' := fun r => φ.commutes (algebraMap K (E' : Type u) r)

/-- The same for an edge residue field.

@census none (helper for `RQ2-2.08`)
-/
noncomputable def restrictEdgeEmb (c : Y.edgeIndexSet)
    (φ : Y.residueField c →ₐ[(E' : Type u)] L) :
    (EtaleSpecies.restriction (K := K) Y).residueField c →ₐ[K] L where
  toFun := φ
  map_one' := φ.map_one
  map_mul' := φ.map_mul
  map_zero' := φ.map_zero
  map_add' := φ.map_add
  commutes' := fun r => φ.commutes (algebraMap K (E' : Type u) r)

variable (E' Y)

/-- The vertex comparison `Gal(L/K) ×_{Gal(L/E')} V(Γ_{E'}(Y)) → V(Γ_K(res Y))`.

@census none (helper for `RQ2-2.08`)
-/
noncomputable def indToVertex :
    InducedSet (galRestrict K L E') (Y.vertexSet L) →
      (EtaleSpecies.restriction (K := K) Y).vertexSet L :=
  Quotient.lift
    (fun p : Gal(L/K) × Y.vertexSet L =>
      (⟨p.2.1, p.1 • restrictVertexEmb (K := K) p.2.1 p.2.2⟩ :
        (EtaleSpecies.restriction (K := K) Y).vertexSet L))
    (by
      rintro ⟨g, ⟨i, φ⟩⟩ ⟨g', v'⟩ ⟨h, hh⟩
      rw [Prod.mk.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      refine Sigma.ext rfl (heq_of_eq (AlgHom.ext fun x => ?_))
      show g (φ x) = g (((galRestrict K L E' h)⁻¹) (h (φ x)))
      rw [show ((galRestrict K L E' h)⁻¹) (h (φ x)) = φ x from
        (galRestrict K L E' h).symm_apply_apply (φ x)])

/-- The edge comparison `Gal(L/K) ×_{Gal(L/E')} E(Γ_{E'}(Y)) → E(Γ_K(res Y))`.

@census none (helper for `RQ2-2.08`)
-/
noncomputable def indToEdge :
    InducedSet (galRestrict K L E') (Y.edgeSet L) →
      (EtaleSpecies.restriction (K := K) Y).edgeSet L :=
  Quotient.lift
    (fun p : Gal(L/K) × Y.edgeSet L =>
      (⟨p.2.1, p.1 • restrictEdgeEmb (K := K) p.2.1 p.2.2⟩ :
        (EtaleSpecies.restriction (K := K) Y).edgeSet L))
    (by
      rintro ⟨g, ⟨c, φ⟩⟩ ⟨g', e'⟩ ⟨h, hh⟩
      rw [Prod.mk.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      refine Sigma.ext rfl (heq_of_eq (AlgHom.ext fun x => ?_))
      show g (φ x) = g (((galRestrict K L E' h)⁻¹) (h (φ x)))
      rw [show ((galRestrict K L E' h)⁻¹) (h (φ x)) = φ x from
        (galRestrict K L E' h).symm_apply_apply (φ x)])

/-- The vertex comparison is a bijection.

@census none (helper for `RQ2-2.08`)
-/
theorem indToVertex_bijective (hY : Y.IsSplitBy L) :
    Function.Bijective (indToVertex E' Y) := by
  constructor
  · refine Quotient.ind₂ ?_
    rintro ⟨g, ⟨i, φ⟩⟩ ⟨g', ⟨i', φ'⟩⟩ heq
    have hi : i = i' := congrArg Sigma.fst heq
    subst hi
    have hsnd : g • restrictVertexEmb (K := K) i φ = g' • restrictVertexEmb (K := K) i φ' :=
      sigma_snd_eq (A := fun i : Y.I => (EtaleSpecies.restriction (K := K) Y).L i →ₐ[K] L)
        (i := i) heq
    have hf : ∀ x : Y.L i, g (φ x) = g' (φ' x) := fun x =>
      congrArg (fun f : (EtaleSpecies.restriction (K := K) Y).L i →ₐ[K] L => f x) hsnd
    obtain ⟨h, hg, hφ⟩ := exists_gal_of_eq φ φ' g g' hf
    refine Quotient.sound ⟨h, ?_⟩
    rw [Prod.mk.injEq]
    exact ⟨by rw [hg, map_inv], Sigma.ext rfl (heq_of_eq hφ)⟩
  · rintro ⟨i, ψ⟩
    obtain ⟨φ₀⟩ := (Y.vertexFiber_single_orbit L hY i).1
    obtain ⟨g, hg⟩ := EtaleSpecies.exists_galois_comp_eq L
      ((EtaleSpecies.restriction (K := K) Y).L i) (restrictVertexEmb (K := K) i φ₀) ψ
    exact ⟨Quotient.mk _ (g, ⟨i, φ₀⟩), Sigma.ext rfl (heq_of_eq hg)⟩

/-- Every residue field of a species split by `L` embeds into `L`; the surjectivity half of
`RQ2-2.11`, isolated.

@census none (helper for `RQ2-2.08`)
-/
theorem nonempty_residueField_emb (hY : Y.IsSplitBy L) (c : Y.edgeIndexSet) :
    Nonempty (Y.residueField c →ₐ[(E' : Type u)] L) := by
  haveI := hY.galois
  haveI := hY.findim
  exact IntermediateField.nonempty_algHom_of_adjoin_splits
    (F := (E' : Type u)) (E := Y.residueField c) (K := L)
    (S := (Set.univ : Set (Y.residueField c)))
    (fun x _ => ⟨Algebra.IsIntegral.isIntegral x, Y.splits_minpoly_residueField L hY c x⟩)
    (IntermediateField.adjoin_univ _ _)

/-- The edge comparison is a bijection.

@census none (helper for `RQ2-2.08`)
-/
theorem indToEdge_bijective (hY : Y.IsSplitBy L) :
    Function.Bijective (indToEdge E' Y) := by
  constructor
  · refine Quotient.ind₂ ?_
    rintro ⟨g, ⟨c, φ⟩⟩ ⟨g', ⟨c', φ'⟩⟩ heq
    have hc : c = c' := congrArg Sigma.fst heq
    subst hc
    have hsnd : g • restrictEdgeEmb (K := K) c φ = g' • restrictEdgeEmb (K := K) c φ' :=
      sigma_snd_eq
        (A := fun c : Y.edgeIndexSet =>
          (EtaleSpecies.restriction (K := K) Y).residueField c →ₐ[K] L) (i := c) heq
    have hf : ∀ x : Y.residueField c, g (φ x) = g' (φ' x) := fun x =>
      congrArg
        (fun f : (EtaleSpecies.restriction (K := K) Y).residueField c →ₐ[K] L => f x) hsnd
    obtain ⟨h, hg, hφ⟩ := exists_gal_of_eq φ φ' g g' hf
    refine Quotient.sound ⟨h, ?_⟩
    rw [Prod.mk.injEq]
    exact ⟨by rw [hg, map_inv], Sigma.ext rfl (heq_of_eq hφ)⟩
  · rintro ⟨c, ψ⟩
    obtain ⟨φ₀⟩ := nonempty_residueField_emb E' Y hY c
    obtain ⟨g, hg⟩ := EtaleSpecies.exists_galois_comp_eq L
      ((EtaleSpecies.restriction (K := K) Y).residueField c) (restrictEdgeEmb (K := K) c φ₀) ψ
    exact ⟨Quotient.mk _ (g, ⟨c, φ₀⟩), Sigma.ext rfl (heq_of_eq hg)⟩

/-- **The restriction of a species split by `L` is again split by `L`.** Every vertex field embeds
into `L` over `E'`, hence over `K`, and `L/K` is normal; every edge algebra injects into a finite
product of copies of `L` through its residue fields.

@census none (helper for `RQ2-2.08`)
-/
theorem restriction_isSplitBy (hY : Y.IsSplitBy L) :
    (EtaleSpecies.restriction (K := K) Y).IsSplitBy L := by
  haveI : Normal K L := IsGalois.to_normal
  refine { galois := inferInstance, findim := inferInstance, splits_L := ?_, splits_M := ?_ }
  · intro i x
    obtain ⟨φ⟩ := (Y.vertexFiber_single_orbit L hY i).1
    exact SplitAlg.splits_of_embedding (restrictVertexEmb (K := K) i φ) x
  · intro i j x
    have τ : ∀ ε : MaximalSpectrum (Y.M i j),
        (EtaleSpecies.restriction (K := K) Y).residueField ⟨(i, j), ε⟩ →ₐ[K] L :=
      fun ε => restrictEdgeEmb (K := K) ⟨(i, j), ε⟩
        (nonempty_residueField_emb E' Y hY ⟨(i, j), ε⟩).some
    set ψ : (EtaleSpecies.restriction (K := K) Y).M i j →ₐ[K] (MaximalSpectrum (Y.M i j) → L) :=
      Pi.algHom K (fun _ => L) (fun ε =>
        (τ ε).comp ((EtaleSpecies.restriction (K := K) Y).residueMap ⟨(i, j), ε⟩)) with hψ
    have hinj : Function.Injective ψ := by
      intro a b hab
      refine ((EtaleSpecies.restriction (K := K) Y).prodDecompositionEquiv i j).injective ?_
      funext ε
      exact (τ ε).injective (congrFun hab ε)
    exact SplitAlg.splits_of_pi_injective ψ hinj x

open CategoryTheory in
/-- The comparison morphism of `K`-rational quivers `res_{E'/K}(Γ_{E'}(Y)) ⟶ Γ_K(res_{E'/K} Y)`.
All four obligations — the two compatibility squares and the two equivariances — are `rfl`: on both
sides `s` and `t` are precomposition with the structure maps and the action is postcomposition
with a Galois element, and the restriction changes neither.

@census none (helper for `RQ2-2.08`)
-/
noncomputable def restrictionQuiverHom (hY : Y.IsSplitBy L) :
    (RationalQuiver.restriction K L E').obj (Y.toRationalQuiver L hY) ⟶
      (EtaleSpecies.restriction (K := K) Y).toRationalQuiver L
        (restriction_isSplitBy E' Y hY) where
  toRQuiverHom :=
    { onV := indToVertex E' Y
      onE := indToEdge E' Y
      onV_source := by refine Quotient.ind ?_; rintro ⟨g, e⟩; rfl
      onV_target := by refine Quotient.ind ?_; rintro ⟨g, e⟩; rfl }
  equivariant_V := by refine fun σ => Quotient.ind ?_; rintro ⟨g, v⟩; rfl
  equivariant_E := by refine fun σ => Quotient.ind ?_; rintro ⟨g, e⟩; rfl

open CategoryTheory in
/-- The comparison morphism is an isomorphism of `K`-rational quivers.

@census none (helper for `RQ2-2.08`)
-/
theorem restrictionQuiverHom_isIso (hY : Y.IsSplitBy L) :
    IsIso (restrictionQuiverHom E' Y hY) :=
  RationalQuiver.isIso_of_bijective _ (indToVertex_bijective E' Y hY) (indToEdge_bijective E' Y hY)

end

end RestrictionIso


/-! ## Transitivity of base change (`RQ2-2.34`), the index and vertex comparison

`RQ2-2.34` quantifies over **arbitrary** field extensions `N'/N/K` — no finiteness, no
separability, no intermediate field of a Galois extension — so the anti-equivalence `RQ2-2.13` and
the two agreement theorems of `RQ2-2.08`, which live over an `E' : IntermediateField K L` with `L/K`
finite Galois, cannot reach it: `K = ℚ`, `N = ℚ(t)`, `N' = ℚ(t,s)` is inside this statement's
domain and outside theirs. The route is therefore the direct one `MD-S3-09` anticipated.

The comparison of index sets is a comparison of two decompositions of the **same** algebra
`N' ⊗_K L_i`: the direct one, `∏_{k' ∈ J'(i)} L'_{k'}`, and the two-step one obtained by cancelling
the middle base change (`transCan`), splitting `N ⊗_K L_i`, and distributing `N' ⊗_N (−)` over the
resulting finite product (`transSplit`). `PiSplit.splitting_match` then does the rest: the index of
a summand is determined by the kernel of its projection, so the index map matching kernels is a
bijection.
-/

namespace EtaleSpecies

open scoped TensorProduct

section TensorSurj
variable {R S A B C : Type u} [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [Algebra R A]
  [Algebra S A] [IsScalarTower R S A] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

theorem tensorMap_id_surjective (g : B →ₐ[R] C) (hg : Function.Surjective g) :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id S A) g) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a c =>
      obtain ⟨b, rfl⟩ := hg c
      exact ⟨a ⊗ₜ[R] b, rfl⟩
  | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩

end TensorSurj

section Trans
variable {K : Type u} [Field K] (S : EtaleSpecies.{u} K)
  (N : Type u) [Field N] [Algebra K N] (N' : Type u) [Field N'] [Algebra K N'] [Algebra N N']
  [IsScalarTower K N N']

/-- The canonical identification `N' ⊗_N (N ⊗_K X) ≅ N' ⊗_K X`.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transCan (K N N' X : Type u) [Field K] [Field N] [Field N'] [Algebra K N]
    [Algebra K N'] [Algebra N N'] [IsScalarTower K N N'] [CommRing X] [Algebra K X] :
    N' ⊗[N] (N ⊗[K] X) ≃ₐ[N'] N' ⊗[K] X :=
  Algebra.TensorProduct.cancelBaseChange K N N' N' X

/-- The projection of `N' ⊗_K L_i` onto a summand of the **two-step** base change.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def bigProj (κ : (S.baseChange N).baseChangeIndex N') :
    S.vertexAlg N' κ.1.1 →ₐ[N'] (S.baseChange N).baseChangeField N' κ :=
  ((S.baseChange N).baseChangeProj N' κ).comp
    ((Algebra.TensorProduct.map (AlgHom.id N' N') (S.baseChangeProj N κ.1)).comp
      (transCan K N N' (S.L κ.1.1)).symm.toAlgHom)

theorem bigProj_surjective (κ : (S.baseChange N).baseChangeIndex N') :
    Function.Surjective (S.bigProj N N' κ) := by
  intro y
  obtain ⟨z, hz⟩ := (S.baseChange N).baseChangeProj_surjective N' κ y
  obtain ⟨w, hw⟩ := tensorMap_id_surjective (S := N')
    (S.baseChangeProj N κ.1) (S.baseChangeProj_surjective N κ.1) z
  obtain ⟨v, hv⟩ := (transCan K N N' (S.L κ.1.1)).symm.surjective w
  refine ⟨v, ?_⟩
  show (S.baseChange N).baseChangeProj N' κ
    ((Algebra.TensorProduct.map (AlgHom.id N' N') (S.baseChangeProj N κ.1))
      ((transCan K N N' (S.L κ.1.1)).symm v)) = y
  rw [hv, hw, hz]

/-- The **two-step** splitting of `N' ⊗_K L_i`: cancel the middle base change, split `N ⊗_K L_i`,
and distribute `N' ⊗_N (−)` over the finite product.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transSplit (i : S.I) :
    S.vertexAlg N' i ≃ₐ[N']
      (∀ k : (S.vertexSplitting N i).J,
        (S.baseChange N).vertexAlg N' (⟨i, k⟩ : S.baseChangeIndex N)) :=
  letI := Fintype.ofFinite (S.vertexSplitting N i).J
  letI := Classical.decEq (S.vertexSplitting N i).J
  (transCan K N N' (S.L i)).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : N' ≃ₐ[N'] N')
        (S.vertexSplitting N i).equiv).trans
      (Algebra.TensorProduct.piRight N N' N' (S.vertexSplitting N i).F))

theorem transSplit_apply (i : S.I) (k : (S.vertexSplitting N i).J)
    (y : N' ⊗[N] (S.vertexAlg N i)) :
    S.transSplit N N' i ((transCan K N N' (S.L i)) y) k
      = (Algebra.TensorProduct.map (AlgHom.id N' N')
          (S.baseChangeProj N (⟨i, k⟩ : S.baseChangeIndex N))) y := by
  letI := Fintype.ofFinite (S.vertexSplitting N i).J
  letI := Classical.decEq (S.vertexSplitting N i).J
  show (Algebra.TensorProduct.piRight N N' N' (S.vertexSplitting N i).F)
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : N' ≃ₐ[N'] N') (S.vertexSplitting N i).equiv)
        ((transCan K N N' (S.L i)).symm ((transCan K N N' (S.L i)) y))) k = _
  rw [AlgEquiv.symm_apply_apply]
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]; exact (map_zero _).symm
  | tmul n a =>
      rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.piRight_tmul]
      rfl
  | add x y hx hy => rw [map_add, map_add, Pi.add_apply, hx, hy]; exact (map_add _ _ _).symm

theorem bigProj_eq (κ : (S.baseChange N).baseChangeIndex N') (x : S.vertexAlg N' κ.1.1) :
    S.bigProj N N' κ x
      = (S.baseChange N).baseChangeProj N' κ (S.transSplit N N' κ.1.1 x κ.1.2) := by
  have h := S.transSplit_apply N N' κ.1.1 κ.1.2 ((transCan K N N' (S.L κ.1.1)).symm x)
  rw [AlgEquiv.apply_symm_apply] at h
  exact congrArg ((S.baseChange N).baseChangeProj N' κ) h.symm

/-- The fibre over `i` of the two-step index set.

@census none (helper for `RQ2-2.34`)
-/
abbrev transFib (i : S.I) : Type u :=
  Σ k : (S.vertexSplitting N i).J,
    ((S.baseChange N).vertexSplitting N' (⟨i, k⟩ : S.baseChangeIndex N)).J

/-- The index in `transFib` as a point of the two-step index set.

@census none (helper for `RQ2-2.34`)
-/
abbrev transFibIdx {i : S.I} (d : transFib S N N' i) : (S.baseChange N).baseChangeIndex N' :=
  ⟨⟨i, d.1⟩, d.2⟩

/-- The projection of `N' ⊗_K L_i` onto the summand indexed by `d`.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transFibProj (i : S.I) (d : transFib S N N' i) :
    S.vertexAlg N' i →ₐ[N'] (S.baseChange N).baseChangeField N' (transFibIdx S N N' d) :=
  S.bigProj N N' (transFibIdx S N N' d)

theorem ker_eq_of_comp_surjective {R A B C D : Type u} [CommRing R] [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (w : A →ₐ[R] B) (hw : Function.Surjective w) (f : B →ₐ[R] C) (g : B →ₐ[R] D)
    (h : RingHom.ker (f.comp w) = RingHom.ker (g.comp w)) :
    RingHom.ker f = RingHom.ker g := by
  ext y
  obtain ⟨x, rfl⟩ := hw y
  constructor
  · intro hy
    have hx : x ∈ RingHom.ker (f.comp w) := hy
    rw [h] at hx
    exact hx
  · intro hy
    have hx : x ∈ RingHom.ker (g.comp w) := hy
    rw [← h] at hx
    exact hx

/-- The `k`-th component of the two-step splitting, as an algebra map.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transSplitProj (i : S.I) (k : (S.vertexSplitting N i).J) :
    S.vertexAlg N' i →ₐ[N'] (S.baseChange N).vertexAlg N' (⟨i, k⟩ : S.baseChangeIndex N) :=
  (Pi.evalAlgHom N' _ k).comp (S.transSplit N N' i).toAlgHom

theorem transSplitProj_surjective (i : S.I) (k : (S.vertexSplitting N i).J) :
    Function.Surjective (S.transSplitProj N N' i k) := by
  intro z
  obtain ⟨y, hy⟩ := Function.surjective_eval
    (β := fun k => (S.baseChange N).vertexAlg N' (⟨i, k⟩ : S.baseChangeIndex N)) k z
  refine ⟨(S.transSplit N N' i).symm y, ?_⟩
  show (S.transSplit N N' i) ((S.transSplit N N' i).symm y) k = z
  rw [AlgEquiv.apply_symm_apply]
  exact hy

theorem bigProj_factors (i : S.I) (d : transFib S N N' i) :
    S.bigProj N N' (transFibIdx S N N' d)
      = ((S.baseChange N).baseChangeProj N' (transFibIdx S N N' d)).comp
        (S.transSplitProj N N' i d.1) :=
  AlgHom.ext fun x => S.bigProj_eq N N' (transFibIdx S N N' d) x

theorem transFib_ker_inj (i : S.I) :
    Function.Injective (fun d : transFib S N N' i =>
      RingHom.ker (S.transFibProj N N' i d)) := by
  classical
  rintro ⟨k₁, m₁⟩ ⟨k₂, m₂⟩ h
  have h' : RingHom.ker (S.bigProj N N' (transFibIdx S N N' (⟨k₁, m₁⟩ : transFib S N N' i)))
      = RingHom.ker (S.bigProj N N' (transFibIdx S N N' (⟨k₂, m₂⟩ : transFib S N N' i))) := h
  have hk : k₁ = k₂ := by
    by_contra hne
    have h1 : S.bigProj N N' (transFibIdx S N N' (⟨k₁, m₁⟩ : transFib S N N' i))
        ((S.transSplit N N' i).symm (Pi.single k₁ 1)) = 1 := by
      rw [S.bigProj_eq N N' (transFibIdx S N N' (⟨k₁, m₁⟩ : transFib S N N' i)),
        AlgEquiv.apply_symm_apply, Pi.single_eq_same]
      exact map_one _
    have h2 : S.bigProj N N' (transFibIdx S N N' (⟨k₂, m₂⟩ : transFib S N N' i))
        ((S.transSplit N N' i).symm (Pi.single k₁ 1)) = 0 := by
      rw [S.bigProj_eq N N' (transFibIdx S N N' (⟨k₂, m₂⟩ : transFib S N N' i)),
        AlgEquiv.apply_symm_apply, Pi.single_eq_of_ne (Ne.symm hne)]
      exact map_zero _
    have hmem : (S.transSplit N N' i).symm (Pi.single k₁ 1)
        ∈ RingHom.ker (S.bigProj N N' (transFibIdx S N N' (⟨k₂, m₂⟩ : transFib S N N' i))) := h2
    rw [← h'] at hmem
    exact one_ne_zero (h1.symm.trans hmem)
  subst hk
  rw [S.bigProj_factors N N' i (⟨k₁, m₁⟩ : transFib S N N' i),
    S.bigProj_factors N N' i (⟨k₁, m₂⟩ : transFib S N N' i)] at h'
  have hker2 := ker_eq_of_comp_surjective (S.transSplitProj N N' i k₁)
    (S.transSplitProj_surjective N N' i k₁) _ _ h'
  exact congrArg (Sigma.mk k₁)
    ((S.baseChange N).baseChangeProj_ker_inj N' (⟨i, k₁⟩ : S.baseChangeIndex N) hker2)


theorem ker_comp_injective {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : B →ₐ[R] C) (hf : Function.Injective f)
    (g : A →ₐ[R] B) : RingHom.ker (f.comp g) = RingHom.ker g := by
  ext x
  show f (g x) = 0 ↔ g x = 0
  exact map_eq_zero_iff _ hf

theorem transFib_ker_surj (i : S.I) (k' : (S.vertexSplitting N' i).J) :
    ∃ d : transFib S N N' i,
      RingHom.ker (S.baseChangeProj N' (⟨i, k'⟩ : S.baseChangeIndex N'))
        = RingHom.ker (S.transFibProj N N' i d) := by
  obtain ⟨k, φ, hφ⟩ := PiSplit.exists_pi_factor'
    (N := N') (F := fun k => (S.baseChange N).vertexAlg N' (⟨i, k⟩ : S.baseChangeIndex N))
    (B := S.baseChangeField N' (⟨i, k'⟩ : S.baseChangeIndex N'))
    ((S.baseChangeProj N' (⟨i, k'⟩ : S.baseChangeIndex N')).comp
      (S.transSplit N N' i).symm.toAlgHom)
  have hq : ∀ x, S.baseChangeProj N' (⟨i, k'⟩ : S.baseChangeIndex N') x
      = φ ((S.transSplit N N' i) x k) := by
    intro x
    have hx := AlgHom.ext_iff.mp hφ ((S.transSplit N N' i) x)
    have he : (S.transSplit N N' i).symm ((S.transSplit N N' i) x) = x :=
      (S.transSplit N N' i).symm_apply_apply x
    exact (congrArg (S.baseChangeProj N' (⟨i, k'⟩ : S.baseChangeIndex N')) he).symm.trans hx
  set m := (S.baseChange N).bcFactorIndex N' (⟨i, k⟩ : S.baseChangeIndex N) φ with hm
  have hbc := (S.baseChange N).bcFactor_spec N' (⟨i, k⟩ : S.baseChangeIndex N) φ
  have key : ∀ x, S.baseChangeProj N' (⟨i, k'⟩ : S.baseChangeIndex N') x
      = ((S.baseChange N).bcFactorHom N' (⟨i, k⟩ : S.baseChangeIndex N) φ)
        (S.bigProj N N' (transFibIdx S N N' (⟨k, m⟩ : transFib S N N' i)) x) := by
    intro x
    rw [hq x, S.bigProj_eq N N' (transFibIdx S N N' (⟨k, m⟩ : transFib S N N' i)) x]
    exact (AlgHom.ext_iff.mp hbc ((S.transSplit N N' i) x k)).symm
  refine ⟨⟨k, m⟩, ?_⟩
  have hfac : S.baseChangeProj N' (⟨i, k'⟩ : S.baseChangeIndex N')
      = ((S.baseChange N).bcFactorHom N' (⟨i, k⟩ : S.baseChangeIndex N) φ).comp
        (S.transFibProj N N' i (⟨k, m⟩ : transFib S N N' i)) := AlgHom.ext key
  rw [hfac]
  exact ker_comp_injective _
    ((S.baseChange N).bcFactorHom N' (⟨i, k⟩ : S.baseChangeIndex N) φ).injective _

theorem transFib_bijective (i : S.I) :
    Function.Bijective (fun d : transFib S N N' i =>
      S.bcFactorIndex N' i (S.transFibProj N N' i d)) :=
  PiSplit.splitting_match (S.vertexSplitting N' i).equiv (S.transFibProj N N' i)
    (S.transFib_ker_inj N N' i) (S.transFib_ker_surj N N' i) _
    (fun d => S.bcFactor_ker N' i (S.transFibProj N N' i d))

/-- The index component of the transitivity comparison.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transOnI (κ : (S.baseChange N).baseChangeIndex N') : S.baseChangeIndex N' :=
  ⟨κ.1.1, S.bcFactorIndex N' κ.1.1 (S.bigProj N N' κ)⟩

/-- Its algebra component.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transOnL (κ : (S.baseChange N).baseChangeIndex N') :
    S.baseChangeField N' (S.transOnI N N' κ) →ₐ[N'] (S.baseChange N).baseChangeField N' κ :=
  S.bcFactorHom N' κ.1.1 (S.bigProj N N' κ)

theorem transOnL_proj (κ : (S.baseChange N).baseChangeIndex N')
    (x : S.vertexAlg N' κ.1.1) :
    S.transOnL N N' κ (S.baseChangeProj N' (S.transOnI N N' κ) x) = S.bigProj N N' κ x :=
  AlgHom.ext_iff.mp (S.bcFactor_spec N' κ.1.1 (S.bigProj N N' κ)) x

theorem transOnL_bijective (κ : (S.baseChange N).baseChangeIndex N') :
    Function.Bijective (S.transOnL N N' κ) := by
  refine ⟨(S.transOnL N N' κ).injective, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := S.bigProj_surjective N N' κ y
  exact ⟨S.baseChangeProj N' (S.transOnI N N' κ) x, (S.transOnL_proj N N' κ x).trans hx⟩

theorem transOnI_bijective : Function.Bijective (S.transOnI N N') := by
  constructor
  · rintro ⟨⟨i₁, k₁⟩, m₁⟩ ⟨⟨i₂, k₂⟩, m₂⟩ h
    have hi : i₁ = i₂ := congrArg Sigma.fst h
    subst hi
    have hd : S.bcFactorIndex N' i₁ (S.transFibProj N N' i₁ (⟨k₁, m₁⟩ : transFib S N N' i₁))
        = S.bcFactorIndex N' i₁ (S.transFibProj N N' i₁ (⟨k₂, m₂⟩ : transFib S N N' i₁)) :=
      sigma_snd_eq (A := fun i : S.I => (S.vertexSplitting N' i).J) (i := i₁) h
    have hthis := (S.transFib_bijective N N' i₁).1 hd
    rw [Sigma.mk.injEq] at hthis
    obtain ⟨hk, hm⟩ := hthis
    subst hk
    have hm' : m₁ = m₂ := eq_of_heq hm
    subst hm'
    rfl
  · rintro ⟨i, k'⟩
    obtain ⟨d, hd⟩ := (S.transFib_bijective N N' i).2 k'
    exact ⟨⟨⟨i, d.1⟩, d.2⟩, Sigma.ext rfl (heq_of_eq hd)⟩

end Trans

section TransEdge
variable {K : Type u} [Field K] (S : EtaleSpecies.{u} K)
  (N : Type u) [Field N] [Algebra K N] (N' : Type u) [Field N'] [Algebra K N'] [Algebra N N']
  [IsScalarTower K N N']

/-- The middle comparison `N' ⊗_K {}_iM_j → N' ⊗_N {}_kM'_ℓ`.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transMid (k l : S.baseChangeIndex N) :
    S.edgeAlg N' k.1 l.1 →ₐ[N'] (S.baseChange N).edgeAlg N' k l :=
  (Algebra.TensorProduct.map (AlgHom.id N' N') (S.edgeMid N k l)).comp
    (transCan K N N' (S.M k.1 l.1)).symm.toAlgHom

theorem transMid_left (k l : S.baseChangeIndex N) (a : S.vertexAlg N' k.1) :
    S.transMid N N' k l (S.edgeHomLeft N' k.1 l.1 a)
      = (S.baseChange N).edgeHomLeft N' k l
          ((Algebra.TensorProduct.map (AlgHom.id N' N') (S.baseChangeProj N k))
            ((transCan K N N' (S.L k.1)).symm a)) := by
  have h : (S.transMid N N' k l).comp (S.edgeHomLeft N' k.1 l.1)
      = ((S.baseChange N).edgeHomLeft N' k l).comp
        ((Algebra.TensorProduct.map (AlgHom.id N' N') (S.baseChangeProj N k)).comp
          (transCan K N N' (S.L k.1)).symm.toAlgHom) := by
    refine Algebra.TensorProduct.ext' fun n x => ?_
    show (n : N') ⊗ₜ[N] (S.edgeMid N k l ((1 : N) ⊗ₜ[K] (S.left k.1 l.1 x)))
      = (n : N') ⊗ₜ[N] ((S.baseChange N).left k l
          (S.baseChangeProj N k ((1 : N) ⊗ₜ[K] x)))
    refine congrArg (fun z => (n : N') ⊗ₜ[N] z) ?_
    rw [S.left_baseChangeProj N k l ((1 : N) ⊗ₜ[K] x)]
    rfl
  exact AlgHom.ext_iff.mp h a

theorem transMid_right (k l : S.baseChangeIndex N) (b : S.vertexAlg N' l.1) :
    S.transMid N N' k l (S.edgeHomRight N' k.1 l.1 b)
      = (S.baseChange N).edgeHomRight N' k l
          ((Algebra.TensorProduct.map (AlgHom.id N' N') (S.baseChangeProj N l))
            ((transCan K N N' (S.L l.1)).symm b)) := by
  have h : (S.transMid N N' k l).comp (S.edgeHomRight N' k.1 l.1)
      = ((S.baseChange N).edgeHomRight N' k l).comp
        ((Algebra.TensorProduct.map (AlgHom.id N' N') (S.baseChangeProj N l)).comp
          (transCan K N N' (S.L l.1)).symm.toAlgHom) := by
    refine Algebra.TensorProduct.ext' fun n x => ?_
    show (n : N') ⊗ₜ[N] (S.edgeMid N k l ((1 : N) ⊗ₜ[K] (S.right k.1 l.1 x)))
      = (n : N') ⊗ₜ[N] ((S.baseChange N).right k l
          (S.baseChangeProj N l ((1 : N) ⊗ₜ[K] x)))
    refine congrArg (fun z => (n : N') ⊗ₜ[N] z) ?_
    rw [S.right_baseChangeProj N k l ((1 : N) ⊗ₜ[K] x)]
    rfl
  exact AlgHom.ext_iff.mp h b

/-- The middle datum of the transitivity comparison on edges.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transG (s t : (S.baseChange N).baseChangeIndex N') :
    S.edgeAlg N' s.1.1 t.1.1 →ₐ[N'] ((S.baseChange N).baseChange N').M s t :=
  ((S.baseChange N).edgeMid N' s t).comp (S.transMid N N' s.1 t.1)

theorem transHk (s t : (S.baseChange N).baseChangeIndex N')
    (a : S.vertexAlg N' (S.transOnI N N' s).1) :
    (((S.baseChange N).baseChange N').left s t)
        (S.transOnL N N' s (S.baseChangeProj N' (S.transOnI N N' s) a))
      = S.transG N N' s t (S.edgeHomLeft N' s.1.1 t.1.1 a) := by
  rw [S.transOnL_proj N N' s a]
  show (((S.baseChange N).baseChange N').left s t)
      ((S.baseChange N).baseChangeProj N' s
        ((Algebra.TensorProduct.map (AlgHom.id N' N') (S.baseChangeProj N s.1))
          ((transCan K N N' (S.L s.1.1)).symm a))) = _
  rw [(S.baseChange N).left_baseChangeProj N' s t _]
  show _ = (S.baseChange N).edgeMid N' s t
    (S.transMid N N' s.1 t.1 (S.edgeHomLeft N' s.1.1 t.1.1 a))
  rw [S.transMid_left N N' s.1 t.1 a]
  rfl

theorem transHl (s t : (S.baseChange N).baseChangeIndex N')
    (b : S.vertexAlg N' (S.transOnI N N' t).1) :
    (((S.baseChange N).baseChange N').right s t)
        (S.transOnL N N' t (S.baseChangeProj N' (S.transOnI N N' t) b))
      = S.transG N N' s t (S.edgeHomRight N' s.1.1 t.1.1 b) := by
  rw [S.transOnL_proj N N' t b]
  show (((S.baseChange N).baseChange N').right s t)
      ((S.baseChange N).baseChangeProj N' t
        ((Algebra.TensorProduct.map (AlgHom.id N' N') (S.baseChangeProj N t.1))
          ((transCan K N N' (S.L t.1.1)).symm b))) = _
  rw [(S.baseChange N).right_baseChangeProj N' s t _]
  show _ = (S.baseChange N).edgeMid N' s t
    (S.transMid N N' s.1 t.1 (S.edgeHomRight N' s.1.1 t.1.1 b))
  rw [S.transMid_right N N' s.1 t.1 b]
  rfl

/-- The edge component of the transitivity comparison.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transOnM (s t : (S.baseChange N).baseChangeIndex N') :
    (S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t)
      →ₐ[N'] ((S.baseChange N).baseChange N').M s t :=
  edgeLift (S := S) (N := N') (S.transOnI N N' s) (S.transOnI N N' t) (S.transG N N' s t)
    ((((S.baseChange N).baseChange N').left s t).comp (S.transOnL N N' s))
    ((((S.baseChange N).baseChange N').right s t).comp (S.transOnL N N' t))
    (S.transHk N N' s t) (S.transHl N N' s t)

/-- **The transitivity comparison** `S ⊗_K N' ⟶ (S ⊗_K N) ⊗_N N'`.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transHom : (S.baseChange N') ⟶ ((S.baseChange N).baseChange N') where
  onI := S.transOnI N N'
  onL := S.transOnL N N'
  onM := S.transOnM N N'
  compat_left := fun s t => AlgHom.ext fun a =>
    edgeLift_left (S := S) (N := N') (S.transOnI N N' s) (S.transOnI N N' t)
      (S.transG N N' s t)
      ((((S.baseChange N).baseChange N').left s t).comp (S.transOnL N N' s))
      ((((S.baseChange N).baseChange N').right s t).comp (S.transOnL N N' t))
      (S.transHk N N' s t) (S.transHl N N' s t) a
  compat_right := fun s t => AlgHom.ext fun b =>
    edgeLift_right (S := S) (N := N') (S.transOnI N N' s) (S.transOnI N N' t)
      (S.transG N N' s t)
      ((((S.baseChange N).baseChange N').left s t).comp (S.transOnL N N' s))
      ((((S.baseChange N).baseChange N').right s t).comp (S.transOnL N N' t))
      (S.transHk N N' s t) (S.transHl N N' s t) b

end TransEdge

/-! ### The inverse of the edge comparison, and `RQ2-2.34`

`transHom`'s index and vertex components are bijections; its edge component is inverted here by
hand, because `edgeLift` gives maps *out of* an edge algebra in both directions and the two round
trips are then three generator checks each (`baseChangeEdge_hom_ext`). The one new ingredient is
the `N`-algebra structure on an `N'`-algebra (`algOfTower`), which is what lets the inverse's middle
datum be assembled at the `N` level and pushed up by `AlgHom.liftEquiv`.
-/

section TransInv
variable {K : Type u} [Field K] (S : EtaleSpecies.{u} K)
  (N : Type u) [Field N] [Algebra K N] (N' : Type u) [Field N'] [Algebra K N'] [Algebra N N']
  [IsScalarTower K N N']

theorem liftEquiv_tmul {R Sc A B : Type u} [CommRing R] [CommRing Sc] [CommRing A] [CommRing B]
    [Algebra R Sc] [Algebra R A] [Algebra Sc B] [Algebra R B] [IsScalarTower R Sc B]
    (f : A →ₐ[R] B) (c : Sc) (a : A) :
    (AlgHom.liftEquiv R Sc A B) f (c ⊗ₜ[R] a) = c • f a := by
  simp [AlgHom.liftEquiv]

/-- The base-field structure on an algebra over a bigger field, through the tower.

@census none (helper for `RQ2-2.34`)
-/
@[reducible] noncomputable def algOfTower (F E C : Type u) [Field F] [Field E] [Algebra F E]
    [CommRing C] [Algebra E C] : Algebra F C :=
  ((algebraMap E C).comp (algebraMap F E)).toAlgebra

@[reducible] noncomputable def towerOfTower (F E C : Type u) [Field F] [Field E] [Algebra F E]
    [CommRing C] [Algebra E C] :
    letI := algOfTower F E C; IsScalarTower F E C :=
  letI := algOfTower F E C
  IsScalarTower.of_algebraMap_eq' rfl

/-- `N ⊗_K X → N' ⊗_K X`.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transNu (X : Type u) [CommRing X] [Algebra K X] :
    N ⊗[K] X →ₐ[N] N' ⊗[K] X :=
  upgradeBase
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K N N') (AlgHom.id K X)).toRingHom
    (fun n => by
      show (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K N N') (AlgHom.id K X))
        (n ⊗ₜ[K] (1 : X)) = _
      rw [Algebra.TensorProduct.map_tmul]
      rfl)

theorem transNu_edgeHomLeft (i j : S.I) (a : S.vertexAlg N i) :
    S.edgeHomLeft N' i j (transNu N N' (S.L i) a)
      = transNu N N' (S.M i j) (S.edgeHomLeft N i j a) := by
  have h : (AlgHom.restrictScalars N (S.edgeHomLeft N' i j)).comp (transNu N N' (S.L i))
      = (transNu N N' (S.M i j)).comp (S.edgeHomLeft N i j) := by
    refine Algebra.TensorProduct.ext' fun n x => ?_
    show (algebraMap N N' n) ⊗ₜ[K] (S.left i j x) = _
    show _ = (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K N N') (AlgHom.id K (S.M i j)))
      (n ⊗ₜ[K] (S.left i j x))
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  exact AlgHom.ext_iff.mp h a

theorem transNu_edgeHomRight (i j : S.I) (b : S.vertexAlg N j) :
    S.edgeHomRight N' i j (transNu N N' (S.L j) b)
      = transNu N N' (S.M i j) (S.edgeHomRight N i j b) := by
  have h : (AlgHom.restrictScalars N (S.edgeHomRight N' i j)).comp (transNu N N' (S.L j))
      = (transNu N N' (S.M i j)).comp (S.edgeHomRight N i j) := by
    refine Algebra.TensorProduct.ext' fun n x => ?_
    show (algebraMap N N' n) ⊗ₜ[K] (S.right i j x) = _
    show _ = (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K N N') (AlgHom.id K (S.M i j)))
      (n ⊗ₜ[K] (S.right i j x))
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  exact AlgHom.ext_iff.mp h b

theorem transCan_symm_transNu (X : Type u) [CommRing X] [Algebra K X] (a : N ⊗[K] X) :
    (transCan K N N' X).symm (transNu N N' X a) = (1 : N') ⊗ₜ[N] a := by
  have h : (AlgHom.restrictScalars N (transCan K N N' X).symm.toAlgHom).comp (transNu N N' X)
      = (Algebra.TensorProduct.includeRight : (N ⊗[K] X) →ₐ[N] N' ⊗[N] (N ⊗[K] X)) := by
    refine Algebra.TensorProduct.ext' fun n x => ?_
    show (transCan K N N' X).symm ((algebraMap N N' n) ⊗ₜ[K] x) = _
    show (algebraMap N N' n) ⊗ₜ[N] ((1 : N) ⊗ₜ[K] x) = (1 : N') ⊗ₜ[N] (n ⊗ₜ[K] x)
    have h1 : (n ⊗ₜ[K] x : N ⊗[K] X) = n • ((1 : N) ⊗ₜ[K] x) := by
      rw [TensorProduct.smul_tmul']
      congr 1
      rw [Algebra.smul_def, mul_one, Algebra.algebraMap_self_apply]
    rw [h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    rw [Algebra.smul_def, mul_one]
  exact AlgHom.ext_iff.mp h a

/-- `transOnL` as an isomorphism.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transOnLEquiv (s : (S.baseChange N).baseChangeIndex N') :
    S.baseChangeField N' (S.transOnI N N' s) ≃ₐ[N'] (S.baseChange N).baseChangeField N' s :=
  AlgEquiv.ofBijective (S.transOnL N N' s) (S.transOnL_bijective N N' s)

theorem transOnLEquiv_symm_bigProj (s : (S.baseChange N).baseChangeIndex N')
    (x : S.vertexAlg N' s.1.1) :
    (S.transOnLEquiv N N' s).symm (S.bigProj N N' s x)
      = S.baseChangeProj N' (S.transOnI N N' s) x := by
  refine (S.transOnLEquiv N N' s).injective ?_
  rw [AlgEquiv.apply_symm_apply]
  exact (S.transOnL_proj N N' s x).symm

theorem bigProj_transNu (s : (S.baseChange N).baseChangeIndex N') (a : S.vertexAlg N s.1.1) :
    S.bigProj N N' s (transNu N N' (S.L s.1.1) a)
      = (S.baseChange N).baseChangeProj N' s ((1 : N') ⊗ₜ[N] (S.baseChangeProj N s.1 a)) := by
  show (S.baseChange N).baseChangeProj N' s
      ((Algebra.TensorProduct.map (AlgHom.id N' N') (S.baseChangeProj N s.1))
        ((transCan K N N' (S.L s.1.1)).symm (transNu N N' (S.L s.1.1) a))) = _
  rw [transCan_symm_transNu N N' (S.L s.1.1) a]
  rfl

/-- The middle datum of the inverse comparison, at the `N` level.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transGinv (s t : (S.baseChange N).baseChangeIndex N') :
    letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
    S.edgeAlg N s.1.1 t.1.1 →ₐ[N]
      (S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t) :=
  letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  letI := towerOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  (AlgHom.restrictScalars N
    (S.edgeMid N' (S.transOnI N N' s) (S.transOnI N N' t))).comp
      (transNu N N' (S.M s.1.1 t.1.1))

/-- The left datum of the inverse comparison, at the `N` level.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transPsiK (s t : (S.baseChange N).baseChangeIndex N') :
    letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
    (S.baseChange N).L s.1 →ₐ[N]
      (S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t) :=
  letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  letI := towerOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  (AlgHom.restrictScalars N
    (((S.baseChange N').left (S.transOnI N N' s) (S.transOnI N N' t)).comp
      ((S.transOnLEquiv N N' s).symm.toAlgHom.comp
        ((S.baseChange N).baseChangeProj N' s)))).comp
    (Algebra.TensorProduct.includeRight (R := N) (A := N') (B := (S.baseChange N).L s.1))

/-- The right datum of the inverse comparison, at the `N` level.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transPsiL (s t : (S.baseChange N).baseChangeIndex N') :
    letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
    (S.baseChange N).L t.1 →ₐ[N]
      (S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t) :=
  letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  letI := towerOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  (AlgHom.restrictScalars N
    (((S.baseChange N').right (S.transOnI N N' s) (S.transOnI N N' t)).comp
      ((S.transOnLEquiv N N' t).symm.toAlgHom.comp
        ((S.baseChange N).baseChangeProj N' t)))).comp
    (Algebra.TensorProduct.includeRight (R := N) (A := N') (B := (S.baseChange N).L t.1))

theorem transHkInv (s t : (S.baseChange N).baseChangeIndex N') (a : S.vertexAlg N s.1.1) :
    S.transPsiK N N' s t (S.baseChangeProj N s.1 a)
      = S.transGinv N N' s t (S.edgeHomLeft N s.1.1 t.1.1 a) := by
  show ((S.baseChange N').left (S.transOnI N N' s) (S.transOnI N N' t))
      ((S.transOnLEquiv N N' s).symm
        ((S.baseChange N).baseChangeProj N' s
          ((1 : N') ⊗ₜ[N] (S.baseChangeProj N s.1 a)))) = _
  rw [← S.bigProj_transNu N N' s a, S.transOnLEquiv_symm_bigProj N N' s,
    S.left_baseChangeProj N' (S.transOnI N N' s) (S.transOnI N N' t)]
  show (S.edgeMid N' (S.transOnI N N' s) (S.transOnI N N' t))
      ((S.edgeHomLeft N' s.1.1 t.1.1) ((transNu N N' (S.L s.1.1)) a)) = _
  rw [transNu_edgeHomLeft S N N' s.1.1 t.1.1 a]
  rfl

theorem transHlInv (s t : (S.baseChange N).baseChangeIndex N') (b : S.vertexAlg N t.1.1) :
    S.transPsiL N N' s t (S.baseChangeProj N t.1 b)
      = S.transGinv N N' s t (S.edgeHomRight N s.1.1 t.1.1 b) := by
  show ((S.baseChange N').right (S.transOnI N N' s) (S.transOnI N N' t))
      ((S.transOnLEquiv N N' t).symm
        ((S.baseChange N).baseChangeProj N' t
          ((1 : N') ⊗ₜ[N] (S.baseChangeProj N t.1 b)))) = _
  rw [← S.bigProj_transNu N N' t b, S.transOnLEquiv_symm_bigProj N N' t,
    S.right_baseChangeProj N' (S.transOnI N N' s) (S.transOnI N N' t)]
  show (S.edgeMid N' (S.transOnI N N' s) (S.transOnI N N' t))
      ((S.edgeHomRight N' s.1.1 t.1.1) ((transNu N N' (S.L t.1.1)) b)) = _
  rw [transNu_edgeHomRight S N N' s.1.1 t.1.1 b]
  rfl

/-- The inverse comparison at the `N` level.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transH (s t : (S.baseChange N).baseChangeIndex N') :
    letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
    (S.baseChange N).M s.1 t.1 →ₐ[N]
      (S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t) :=
  letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  letI := towerOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  edgeLift (S := S) (N := N) s.1 t.1 (S.transGinv N N' s t) (S.transPsiK N N' s t)
    (S.transPsiL N N' s t) (S.transHkInv N N' s t) (S.transHlInv N N' s t)

/-- The middle datum of the inverse comparison, at the `N'` level.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transGinv' (s t : (S.baseChange N).baseChangeIndex N') :
    (S.baseChange N).edgeAlg N' s.1 t.1 →ₐ[N']
      (S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t) :=
  letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  letI := towerOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  AlgHom.liftEquiv N N' ((S.baseChange N).M s.1 t.1) _ (S.transH N N' s t)

theorem transGinv'_tmul (s t : (S.baseChange N).baseChangeIndex N') (n : N')
    (y : (S.baseChange N).M s.1 t.1) :
    S.transGinv' N N' s t (n ⊗ₜ[N] y) = n • S.transH N N' s t y := by
  letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  letI := towerOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  exact liftEquiv_tmul (S.transH N N' s t) n y

/-- The left datum of the inverse comparison, at the `N'` level.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transPhiKinv (s t : (S.baseChange N).baseChangeIndex N') :
    (S.baseChange N).baseChangeField N' s →ₐ[N']
      (S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t) :=
  ((S.baseChange N').left (S.transOnI N N' s) (S.transOnI N N' t)).comp
    (S.transOnLEquiv N N' s).symm.toAlgHom

/-- The right datum of the inverse comparison, at the `N'` level.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transPhiLinv (s t : (S.baseChange N).baseChangeIndex N') :
    (S.baseChange N).baseChangeField N' t →ₐ[N']
      (S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t) :=
  ((S.baseChange N').right (S.transOnI N N' s) (S.transOnI N N' t)).comp
    (S.transOnLEquiv N N' t).symm.toAlgHom

theorem transH_left (s t : (S.baseChange N).baseChangeIndex N')
    (f : (S.baseChange N).L s.1) :
    S.transH N N' s t ((S.baseChange N).left s.1 t.1 f) = S.transPsiK N N' s t f := by
  letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  letI := towerOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  exact edgeLift_left (S := S) (N := N) s.1 t.1 (S.transGinv N N' s t) (S.transPsiK N N' s t)
    (S.transPsiL N N' s t) (S.transHkInv N N' s t) (S.transHlInv N N' s t) f

theorem transH_right (s t : (S.baseChange N).baseChangeIndex N')
    (f : (S.baseChange N).L t.1) :
    S.transH N N' s t ((S.baseChange N).right s.1 t.1 f) = S.transPsiL N N' s t f := by
  letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  letI := towerOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  exact edgeLift_right (S := S) (N := N) s.1 t.1 (S.transGinv N N' s t) (S.transPsiK N N' s t)
    (S.transPsiL N N' s t) (S.transHkInv N N' s t) (S.transHlInv N N' s t) f

theorem transH_edgeMid (s t : (S.baseChange N).baseChangeIndex N')
    (z : S.edgeAlg N s.1.1 t.1.1) :
    S.transH N N' s t (S.edgeMid N s.1 t.1 z) = S.transGinv N N' s t z := by
  letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  letI := towerOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  exact edgeLift_edgeMid (S := S) (N := N) s.1 t.1 (S.transGinv N N' s t) (S.transPsiK N N' s t)
    (S.transPsiL N N' s t) (S.transHkInv N N' s t) (S.transHlInv N N' s t) z

theorem transHkInv' (s t : (S.baseChange N).baseChangeIndex N')
    (a : (S.baseChange N).vertexAlg N' s.1) :
    S.transPhiKinv N N' s t ((S.baseChange N).baseChangeProj N' s a)
      = S.transGinv' N N' s t ((S.baseChange N).edgeHomLeft N' s.1 t.1 a) := by
  letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  letI := towerOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  have h : (S.transPhiKinv N N' s t).comp ((S.baseChange N).baseChangeProj N' s)
      = (S.transGinv' N N' s t).comp ((S.baseChange N).edgeHomLeft N' s.1 t.1) := by
    refine Algebra.TensorProduct.ext' fun n f => ?_
    have hn : (n ⊗ₜ[N] f : (S.baseChange N).vertexAlg N' s.1) = n • ((1 : N') ⊗ₜ[N] f) := by
      rw [TensorProduct.smul_tmul']
      congr 1
      rw [Algebra.smul_def, mul_one, Algebra.algebraMap_self_apply]
    have e1 : S.transPhiKinv N N' s t
        ((S.baseChange N).baseChangeProj N' s ((1 : N') ⊗ₜ[N] f))
        = S.transH N N' s t ((S.baseChange N).left s.1 t.1 f) := (S.transH_left N N' s t f).symm
    show S.transPhiKinv N N' s t ((S.baseChange N).baseChangeProj N' s (n ⊗ₜ[N] f))
      = S.transGinv' N N' s t
        (n ⊗ₜ[N] ((S.baseChange N).left s.1 t.1 f))
    rw [S.transGinv'_tmul N N' s t n _, ← e1, ← map_smul, ← map_smul, ← hn]
    rfl
  exact AlgHom.ext_iff.mp h a

theorem transHlInv' (s t : (S.baseChange N).baseChangeIndex N')
    (b : (S.baseChange N).vertexAlg N' t.1) :
    S.transPhiLinv N N' s t ((S.baseChange N).baseChangeProj N' t b)
      = S.transGinv' N N' s t ((S.baseChange N).edgeHomRight N' s.1 t.1 b) := by
  letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  letI := towerOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  have h : (S.transPhiLinv N N' s t).comp ((S.baseChange N).baseChangeProj N' t)
      = (S.transGinv' N N' s t).comp ((S.baseChange N).edgeHomRight N' s.1 t.1) := by
    refine Algebra.TensorProduct.ext' fun n f => ?_
    have hn : (n ⊗ₜ[N] f : (S.baseChange N).vertexAlg N' t.1) = n • ((1 : N') ⊗ₜ[N] f) := by
      rw [TensorProduct.smul_tmul']
      congr 1
      rw [Algebra.smul_def, mul_one, Algebra.algebraMap_self_apply]
    have e1 : S.transPhiLinv N N' s t
        ((S.baseChange N).baseChangeProj N' t ((1 : N') ⊗ₜ[N] f))
        = S.transH N N' s t ((S.baseChange N).right s.1 t.1 f) := (S.transH_right N N' s t f).symm
    show S.transPhiLinv N N' s t ((S.baseChange N).baseChangeProj N' t (n ⊗ₜ[N] f))
      = S.transGinv' N N' s t
        (n ⊗ₜ[N] ((S.baseChange N).right s.1 t.1 f))
    rw [S.transGinv'_tmul N N' s t n _, ← e1, ← map_smul, ← map_smul, ← hn]
    rfl
  exact AlgHom.ext_iff.mp h b

/-- The inverse of the edge comparison.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def transOnMinv (s t : (S.baseChange N).baseChangeIndex N') :
    ((S.baseChange N).baseChange N').M s t
      →ₐ[N'] (S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t) :=
  edgeLift (S := S.baseChange N) (N := N') s t (S.transGinv' N N' s t)
    (S.transPhiKinv N N' s t) (S.transPhiLinv N N' s t)
    (S.transHkInv' N N' s t) (S.transHlInv' N N' s t)

theorem transGinv'_transMid (s t : (S.baseChange N).baseChangeIndex N')
    (z : S.edgeAlg N' s.1.1 t.1.1) :
    S.transGinv' N N' s t (S.transMid N N' s.1 t.1 z)
      = S.edgeMid N' (S.transOnI N N' s) (S.transOnI N N' t) z := by
  letI := algOfTower K N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  letI := towerOfTower K N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  have h : (S.transGinv' N N' s t).comp (S.transMid N N' s.1 t.1)
      = S.edgeMid N' (S.transOnI N N' s) (S.transOnI N N' t) := by
    refine Algebra.TensorProduct.ext' fun n m => ?_
    have hz : (n ⊗ₜ[K] m : S.edgeAlg N' s.1.1 t.1.1) = n • ((1 : N') ⊗ₜ[K] m) := by
      rw [TensorProduct.smul_tmul']
      congr 1
      rw [Algebra.smul_def, mul_one, Algebra.algebraMap_self_apply]
    have hmid : S.transMid N N' s.1 t.1 (n ⊗ₜ[K] m)
        = n ⊗ₜ[N] (S.edgeMid N s.1 t.1 ((1 : N) ⊗ₜ[K] m)) := rfl
    have h1 : S.transH N N' s t (S.edgeMid N s.1 t.1 ((1 : N) ⊗ₜ[K] m))
        = S.edgeMid N' (S.transOnI N N' s) (S.transOnI N N' t) ((1 : N') ⊗ₜ[K] m) := by
      refine (S.transH_edgeMid N N' s t ((1 : N) ⊗ₜ[K] m)).trans ?_
      show S.edgeMid N' (S.transOnI N N' s) (S.transOnI N N' t)
        (transNu N N' (S.M s.1.1 t.1.1) ((1 : N) ⊗ₜ[K] m)) = _
      refine congrArg (S.edgeMid N' (S.transOnI N N' s) (S.transOnI N N' t)) ?_
      show (algebraMap N N' (1 : N)) ⊗ₜ[K] m = (1 : N') ⊗ₜ[K] m
      rw [map_one]
    show S.transGinv' N N' s t (S.transMid N N' s.1 t.1 (n ⊗ₜ[K] m)) = _
    rw [hmid, S.transGinv'_tmul N N' s t n _, h1, hz, map_smul]
    rfl
  exact AlgHom.ext_iff.mp h z

theorem transOnM_left (s t : (S.baseChange N).baseChangeIndex N')
    (a : S.baseChangeField N' (S.transOnI N N' s)) :
    S.transOnM N N' s t
        ((S.baseChange N').left (S.transOnI N N' s) (S.transOnI N N' t) a)
      = ((S.baseChange N).baseChange N').left s t (S.transOnL N N' s a) :=
  edgeLift_left (S := S) (N := N') (S.transOnI N N' s) (S.transOnI N N' t) (S.transG N N' s t)
    ((((S.baseChange N).baseChange N').left s t).comp (S.transOnL N N' s))
    ((((S.baseChange N).baseChange N').right s t).comp (S.transOnL N N' t))
    (S.transHk N N' s t) (S.transHl N N' s t) a

theorem transOnM_right (s t : (S.baseChange N).baseChangeIndex N')
    (b : S.baseChangeField N' (S.transOnI N N' t)) :
    S.transOnM N N' s t
        ((S.baseChange N').right (S.transOnI N N' s) (S.transOnI N N' t) b)
      = ((S.baseChange N).baseChange N').right s t (S.transOnL N N' t b) :=
  edgeLift_right (S := S) (N := N') (S.transOnI N N' s) (S.transOnI N N' t) (S.transG N N' s t)
    ((((S.baseChange N).baseChange N').left s t).comp (S.transOnL N N' s))
    ((((S.baseChange N).baseChange N').right s t).comp (S.transOnL N N' t))
    (S.transHk N N' s t) (S.transHl N N' s t) b

theorem transOnM_edgeMid (s t : (S.baseChange N).baseChangeIndex N')
    (z : S.edgeAlg N' s.1.1 t.1.1) :
    S.transOnM N N' s t (S.edgeMid N' (S.transOnI N N' s) (S.transOnI N N' t) z)
      = (S.baseChange N).edgeMid N' s t (S.transMid N N' s.1 t.1 z) :=
  edgeLift_edgeMid (S := S) (N := N') (S.transOnI N N' s) (S.transOnI N N' t) (S.transG N N' s t)
    ((((S.baseChange N).baseChange N').left s t).comp (S.transOnL N N' s))
    ((((S.baseChange N).baseChange N').right s t).comp (S.transOnL N N' t))
    (S.transHk N N' s t) (S.transHl N N' s t) z

theorem transOnMinv_left (s t : (S.baseChange N).baseChangeIndex N')
    (c : (S.baseChange N).baseChangeField N' s) :
    S.transOnMinv N N' s t (((S.baseChange N).baseChange N').left s t c)
      = S.transPhiKinv N N' s t c :=
  edgeLift_left (S := S.baseChange N) (N := N') s t (S.transGinv' N N' s t)
    (S.transPhiKinv N N' s t) (S.transPhiLinv N N' s t)
    (S.transHkInv' N N' s t) (S.transHlInv' N N' s t) c

theorem transOnMinv_right (s t : (S.baseChange N).baseChangeIndex N')
    (c : (S.baseChange N).baseChangeField N' t) :
    S.transOnMinv N N' s t (((S.baseChange N).baseChange N').right s t c)
      = S.transPhiLinv N N' s t c :=
  edgeLift_right (S := S.baseChange N) (N := N') s t (S.transGinv' N N' s t)
    (S.transPhiKinv N N' s t) (S.transPhiLinv N N' s t)
    (S.transHkInv' N N' s t) (S.transHlInv' N N' s t) c

theorem transOnMinv_edgeMid (s t : (S.baseChange N).baseChangeIndex N')
    (w : (S.baseChange N).edgeAlg N' s.1 t.1) :
    S.transOnMinv N N' s t ((S.baseChange N).edgeMid N' s t w) = S.transGinv' N N' s t w :=
  edgeLift_edgeMid (S := S.baseChange N) (N := N') s t (S.transGinv' N N' s t)
    (S.transPhiKinv N N' s t) (S.transPhiLinv N N' s t)
    (S.transHkInv' N N' s t) (S.transHlInv' N N' s t) w

theorem transOnMinv_transOnM (s t : (S.baseChange N).baseChangeIndex N')
    (x : (S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t)) :
    S.transOnMinv N N' s t (S.transOnM N N' s t x) = x := by
  have h : (S.transOnMinv N N' s t).comp (S.transOnM N N' s t)
      = AlgHom.id N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t)) := by
    refine S.baseChangeEdge_hom_ext N' (S.transOnI N N' s) (S.transOnI N N' t) _ _
      (fun a => ?_) (fun z => ?_) (fun b => ?_)
    · show S.transOnMinv N N' s t (S.transOnM N N' s t
        ((S.baseChange N').left (S.transOnI N N' s) (S.transOnI N N' t) a)) = _
      rw [S.transOnM_left N N' s t a, S.transOnMinv_left N N' s t _]
      show ((S.baseChange N').left (S.transOnI N N' s) (S.transOnI N N' t))
        ((S.transOnLEquiv N N' s).symm ((S.transOnLEquiv N N' s) a)) = _
      rw [AlgEquiv.symm_apply_apply]
      rfl
    · show S.transOnMinv N N' s t (S.transOnM N N' s t
        (S.edgeMid N' (S.transOnI N N' s) (S.transOnI N N' t) z)) = _
      rw [S.transOnM_edgeMid N N' s t z, S.transOnMinv_edgeMid N N' s t _,
        S.transGinv'_transMid N N' s t z]
      rfl
    · show S.transOnMinv N N' s t (S.transOnM N N' s t
        ((S.baseChange N').right (S.transOnI N N' s) (S.transOnI N N' t) b)) = _
      rw [S.transOnM_right N N' s t b, S.transOnMinv_right N N' s t _]
      show ((S.baseChange N').right (S.transOnI N N' s) (S.transOnI N N' t))
        ((S.transOnLEquiv N N' t).symm ((S.transOnLEquiv N N' t) b)) = _
      rw [AlgEquiv.symm_apply_apply]
      rfl
  exact AlgHom.ext_iff.mp h x

theorem transOnM_transH (s t : (S.baseChange N).baseChangeIndex N')
    (y : (S.baseChange N).M s.1 t.1) :
    S.transOnM N N' s t (S.transH N N' s t y)
      = (S.baseChange N).edgeMid N' s t ((1 : N') ⊗ₜ[N] y) := by
  letI := algOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  letI := towerOfTower N N' ((S.baseChange N').M (S.transOnI N N' s) (S.transOnI N N' t))
  letI := algOfTower N N' (((S.baseChange N).baseChange N').M s t)
  letI := towerOfTower N N' (((S.baseChange N).baseChange N').M s t)
  have h : (AlgHom.restrictScalars N (S.transOnM N N' s t)).comp (S.transH N N' s t)
      = (AlgHom.restrictScalars N ((S.baseChange N).edgeMid N' s t)).comp
        (Algebra.TensorProduct.includeRight
          (R := N) (A := N') (B := (S.baseChange N).M s.1 t.1)) := by
    refine S.baseChangeEdge_hom_ext N s.1 t.1 _ _ (fun f => ?_) (fun y' => ?_) (fun f => ?_)
    · show S.transOnM N N' s t (S.transH N N' s t ((S.baseChange N).left s.1 t.1 f)) = _
      rw [S.transH_left N N' s t f]
      show S.transOnM N N' s t ((S.baseChange N').left (S.transOnI N N' s) (S.transOnI N N' t)
        ((S.transOnLEquiv N N' s).symm
          ((S.baseChange N).baseChangeProj N' s ((1 : N') ⊗ₜ[N] f)))) = _
      rw [S.transOnM_left N N' s t _]
      show ((S.baseChange N).baseChange N').left s t
        ((S.transOnLEquiv N N' s) ((S.transOnLEquiv N N' s).symm _)) = _
      rw [AlgEquiv.apply_symm_apply,
        (S.baseChange N).left_baseChangeProj N' s t ((1 : N') ⊗ₜ[N] f)]
      rfl
    · show S.transOnM N N' s t (S.transH N N' s t (S.edgeMid N s.1 t.1 y')) = _
      rw [S.transH_edgeMid N N' s t y']
      show S.transOnM N N' s t (S.edgeMid N' (S.transOnI N N' s) (S.transOnI N N' t)
        (transNu N N' (S.M s.1.1 t.1.1) y')) = _
      rw [S.transOnM_edgeMid N N' s t _]
      show (S.baseChange N).edgeMid N' s t
        ((Algebra.TensorProduct.map (AlgHom.id N' N') (S.edgeMid N s.1 t.1))
          ((transCan K N N' (S.M s.1.1 t.1.1)).symm
            (transNu N N' (S.M s.1.1 t.1.1) y'))) = _
      exact congrArg (fun z => (S.baseChange N).edgeMid N' s t
        ((Algebra.TensorProduct.map (AlgHom.id N' N') (S.edgeMid N s.1 t.1)) z))
        (transCan_symm_transNu N N' (S.M s.1.1 t.1.1) y')
    · show S.transOnM N N' s t (S.transH N N' s t ((S.baseChange N).right s.1 t.1 f)) = _
      rw [S.transH_right N N' s t f]
      show S.transOnM N N' s t ((S.baseChange N').right (S.transOnI N N' s) (S.transOnI N N' t)
        ((S.transOnLEquiv N N' t).symm
          ((S.baseChange N).baseChangeProj N' t ((1 : N') ⊗ₜ[N] f)))) = _
      rw [S.transOnM_right N N' s t _]
      show ((S.baseChange N).baseChange N').right s t
        ((S.transOnLEquiv N N' t) ((S.transOnLEquiv N N' t).symm _)) = _
      rw [AlgEquiv.apply_symm_apply,
        (S.baseChange N).right_baseChangeProj N' s t ((1 : N') ⊗ₜ[N] f)]
      rfl
  exact AlgHom.ext_iff.mp h y

theorem transOnM_transGinv' (s t : (S.baseChange N).baseChangeIndex N')
    (w : (S.baseChange N).edgeAlg N' s.1 t.1) :
    S.transOnM N N' s t (S.transGinv' N N' s t w) = (S.baseChange N).edgeMid N' s t w := by
  letI := algOfTower N N' (((S.baseChange N).baseChange N').M s t)
  letI := towerOfTower N N' (((S.baseChange N).baseChange N').M s t)
  have h : (S.transOnM N N' s t).comp (S.transGinv' N N' s t)
      = (S.baseChange N).edgeMid N' s t := by
    refine Algebra.TensorProduct.ext' fun n y => ?_
    have hn : (n ⊗ₜ[N] y : (S.baseChange N).edgeAlg N' s.1 t.1) = n • ((1 : N') ⊗ₜ[N] y) := by
      rw [TensorProduct.smul_tmul']
      congr 1
      rw [Algebra.smul_def, mul_one, Algebra.algebraMap_self_apply]
    show S.transOnM N N' s t (S.transGinv' N N' s t (n ⊗ₜ[N] y)) = _
    rw [S.transGinv'_tmul N N' s t n y, map_smul, S.transOnM_transH N N' s t y, ← map_smul]
    exact congrArg ((S.baseChange N).edgeMid N' s t) hn.symm
  exact AlgHom.ext_iff.mp h w

theorem transOnM_transOnMinv (s t : (S.baseChange N).baseChangeIndex N')
    (y : ((S.baseChange N).baseChange N').M s t) :
    S.transOnM N N' s t (S.transOnMinv N N' s t y) = y := by
  have h : (S.transOnM N N' s t).comp (S.transOnMinv N N' s t)
      = AlgHom.id N' (((S.baseChange N).baseChange N').M s t) := by
    refine (S.baseChange N).baseChangeEdge_hom_ext N' s t _ _
      (fun c => ?_) (fun w => ?_) (fun c => ?_)
    · show S.transOnM N N' s t (S.transOnMinv N N' s t
        (((S.baseChange N).baseChange N').left s t c)) = _
      rw [S.transOnMinv_left N N' s t c]
      show S.transOnM N N' s t ((S.baseChange N').left (S.transOnI N N' s) (S.transOnI N N' t)
        ((S.transOnLEquiv N N' s).symm c)) = _
      rw [S.transOnM_left N N' s t _]
      show ((S.baseChange N).baseChange N').left s t
        ((S.transOnLEquiv N N' s) ((S.transOnLEquiv N N' s).symm c)) = _
      rw [AlgEquiv.apply_symm_apply]
      rfl
    · show S.transOnM N N' s t (S.transOnMinv N N' s t
        ((S.baseChange N).edgeMid N' s t w)) = _
      rw [S.transOnMinv_edgeMid N N' s t w, S.transOnM_transGinv' N N' s t w]
      rfl
    · show S.transOnM N N' s t (S.transOnMinv N N' s t
        (((S.baseChange N).baseChange N').right s t c)) = _
      rw [S.transOnMinv_right N N' s t c]
      show S.transOnM N N' s t ((S.baseChange N').right (S.transOnI N N' s) (S.transOnI N N' t)
        ((S.transOnLEquiv N N' t).symm c)) = _
      rw [S.transOnM_right N N' s t _]
      show ((S.baseChange N).baseChange N').right s t
        ((S.transOnLEquiv N N' t) ((S.transOnLEquiv N N' t).symm c)) = _
      rw [AlgEquiv.apply_symm_apply]
      rfl
  exact AlgHom.ext_iff.mp h y

theorem transOnM_bijective (s t : (S.baseChange N).baseChangeIndex N') :
    Function.Bijective (S.transOnM N N' s t) :=
  Function.bijective_iff_has_inverse.mpr ⟨S.transOnMinv N N' s t,
    S.transOnMinv_transOnM N N' s t, S.transOnM_transOnMinv N N' s t⟩

open CategoryTheory in
theorem transHom_isIso : IsIso (S.transHom N N') :=
  EtaleSpecies.isIso_of_bijective _ (S.transOnI_bijective N N')
    (fun t => S.transOnL_bijective N N' t) (fun s t => S.transOnM_bijective N N' s t)

open CategoryTheory in
/-- **The transitivity isomorphism, named.** This is the `def baseChangeTransIso` the
`@divergence` on `RQ2-2.34` promises as the G4 repair of finding V-2: the `∃` of the census
statement is derived from it, not asserted independently.

@census none (helper for `RQ2-2.34`)
-/
noncomputable def baseChangeTransIso :
    (S.baseChange N') ≅ ((S.baseChange N).baseChange N') :=
  letI := S.transHom_isIso N N'
  asIso (S.transHom N N')

open CategoryTheory in
theorem baseChangeTransIso_hom : (S.baseChangeTransIso N N').hom = S.transHom N N' := rfl

end TransInv




end EtaleSpecies

namespace EtaleSpecies

variable {K : Type u} [Field K] (S : EtaleSpecies.{u} K) (N : Type u) [Field N] [Algebra K N]

/-! ### Transitivity of base change (`RQ2-2.34`) -/

/-- **Remark** (Transitivity of base change, census `RQ2-2.34`).
For any tower `N'/N/K` there is a canonical identification `I_{N'} = (I_N)_{N'}` and a canonical
isomorphism `S ⊗_K N' ≅ (S ⊗_K N) ⊗_N N'` of `N'`-species.

The identification of index sets (clause `RQ2-2.34-C1`) is the bijection `Iso.onI_bijective` extracts
from the isomorphism, so the two clauses are delivered by one statement rather than as unrelated
data.

@census    RQ2-2.34
@source    rmk:basechangetransitivity
@clauses   RQ2-2.34-H1, RQ2-2.34-H2, RQ2-2.34-C1, RQ2-2.34-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION on clauses `RQ2-2.34-C1` and `RQ2-2.34-C2` (finding V-2 of the
G2 verification; the earlier text of this field said "none", which understated the shape).
"Canonical isomorphism of `N'`-species" is rendered as an isomorphism in the category of étale
`N'`-species (`EtaleSpecies.instCategory`, census `RQ2-2.04`) — the right ambient category — and the
"canonical identification of index sets" as that isomorphism's own index component, asserted
bijective, so `C1` is delivered as a consequence of `C2` rather than as an unrelated datum. What is
reformulated is the word **canonical**: the statement asserts only that *some* such isomorphism
exists (`∃ e, …`), not a named one. Canonicity is not a predicate without a naturality statement,
and existence is the accepted G2 shape, but it is less than the source says. The G4 repair is a
named `def baseChangeTransIso` from which this `∃` is derived.
**CORRECTED IN PLACE, 2026-08-31 (coordinator-sanctioned retraction, finding V-S4G4-3;
`workflow/reports/PROCESS-CHANGELOG.md`).** The route actually taken is **direct**, not through
`prop:speciesrestrictionbasechangeadjunction`/the anti-equivalence: finding **S4-F3**
(`workflow/stages/S4/DESIGN-NOTES.md` §25) establishes that route is unavailable to the frozen
statement, which quantifies over *arbitrary* field extensions `N'/N/K` with no finiteness,
separability or intermediate-field hypothesis, while `RQ2-2.08`/`RQ2-2.13` are defined only for an
`E' : IntermediateField K L` with `L/K` finite Galois. The proof instead uses uniqueness of the
decomposition of a finite étale algebra into fields (`PiSplit.splitting_match`,
`PiSplit.ker_proj_injective` — the gap `ledger/MATHLIB-DECISIONS.tsv` `MD-S3-09` records mathlib as
lacking) together with tensor bookkeeping (`transCan`, `transSplit` via
`Algebra.TensorProduct.piRight`) comparing the two decompositions of `N' ⊗_K L_i`. This retraction
in place is ruled by the coordinator under `WORKFLOW.md` §7/R6 (retraction-in-place outranks the
relocation contract's byte-identity certificate, whose evidentiary role completed at verification
`aaf9ae2`); see `workflow/stages/S4/RELOCATION-RQ2-2.34.md` §7 for the discharge accounting and the
new digest. Only this `@divergence` field changes; the statement and every other field are
byte-identical to `aaf9ae2`.
-/
theorem baseChange_trans (N' : Type u) [Field N'] [Algebra K N'] [Algebra N N']
    [IsScalarTower K N N'] :
    ∃ e : (S.baseChange N') ≅ ((S.baseChange N).baseChange N'),
      Function.Bijective (CategoryTheory.Iso.hom e).onI :=
  ⟨S.baseChangeTransIso N N', EtaleSpecies.Iso.onI_bijective _⟩

end EtaleSpecies



/-! ## Restriction and base change for species (census `RQ2-2.08`)

The source proves `prop:speciesrestrictionbasechangeadjunction` **from** the quiver adjunction
`prop:quiverrestrictionbasechangeadjunction` (`RQ2-1.07`, stage S1, landed as real data) "by
observing that the given antiequivalences commute with the corresponding restriction and base
change functors". We follow exactly that route: both species-side functors are *defined* as the
transports of the quiver-side ones along the anti-equivalence of `RQ2-2.13`, and two separate
theorems record that the transported functors agree, on objects, with `RQ2-2.05`'s base change and
`RQ2-2.07`'s restriction — which is the "observing" step, made explicit.
-/

open CategoryTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

/-- The anti-equivalence of `RQ2-2.13`, as data. It inherits the `sorry` of
`speciesAntiEquivalence`; at G4 it becomes a genuine equivalence.

@census none (helper: `RQ2-2.13` as data)
-/
noncomputable def speciesEquiv : RationalQuiver K L ≌ (SplitSpecies K L)ᵒᵖ :=
  (speciesAntiEquivalence K L).2.2.1.choose

/-- `speciesEquiv`'s functor is `S(−)` and its inverse is `Γ_K(−)`: the two halves of clause
`RQ2-2.13-C5`, extracted from the theorem. This is what makes the transports below transports of
the paper's own functors.

@census none (helper: `RQ2-2.13-C5` in usable form)
-/
theorem speciesEquiv_functor_inverse :
    (speciesEquiv K L).functor = toSplitSpeciesFunctor K L ∧
      (speciesEquiv K L).inverse = toQuiverFunctor K L :=
  (speciesAntiEquivalence K L).2.2.1.choose_spec

variable (E' : IntermediateField K L) [FiniteDimensional K E']

/-- **Base change of species**, defined as the transport of `RQ2-1.05`'s base change of quivers
along the anti-equivalence — the source's own route. Note that it is *covariant*: it is the
transport of a covariant functor along two contravariant equivalences.

@census none (clause witness for `RQ2-2.08-C1`)
-/
noncomputable def speciesBaseChange : SplitSpecies K L ⥤ SplitSpecies (E' : Type u) L :=
  Functor.unop ((speciesEquiv K L).inverse ⋙ RationalQuiver.baseChange K L E' ⋙
    (speciesEquiv (E' : Type u) L).functor)

/-- **Restriction of species**, likewise the transport of `RQ2-1.06`'s restriction of quivers.

@census none (clause witness for `RQ2-2.08-C1`)
-/
noncomputable def speciesRestriction : SplitSpecies (E' : Type u) L ⥤ SplitSpecies K L :=
  Functor.unop ((speciesEquiv (E' : Type u) L).inverse ⋙ RationalQuiver.restriction K L E' ⋙
    (speciesEquiv K L).functor)

/-- The transported base change **is** the base change of `RQ2-2.05`, on objects: the "observing
that the antiequivalences commute with the base change functors" step of the source's proof.

Proof plan (G4): both sides have index set the disjoint union of the splittings of `L_i ⊗_K E'`;
under the anti-equivalence a vertex orbit corresponds to a `Gal(L/K)`-orbit of embeddings, and
restricting the action to `Gal(L/E')` splits that orbit into exactly the `Gal(L/E')`-orbits, which
is `eq:speciesvertexdecomposition`.

@census none (clause witness for `RQ2-2.08-C1`)
-/
theorem speciesBaseChange_obj_iso (X : SplitSpecies K L) :
    Nonempty (((speciesBaseChange K L E').obj X).obj ≅ X.obj.baseChange (E' : Type u)) := by
  haveI : IsGalois (E' : Type u) L := IsGalois.tower_top_of_isGalois K (E' : Type u) L
  haveI : FiniteDimensional (E' : Type u) L := inferInstance
  rw [speciesBaseChange, (speciesEquiv_functor_inverse K L).2,
    (speciesEquiv_functor_inverse (E' : Type u) L).1]
  show Nonempty (RationalQuiver.toSpecies
    ((RationalQuiver.baseChange K L E').obj (SplitSpecies.toQuiver X)) ≅ _)
  have hY : (X.obj.baseChange (E' : Type u)).IsSplitBy L :=
    X.obj.baseChange_isSplitBy (E' : Type u) X.property
  haveI := EtaleSpecies.bcQuiverHom_isIso X.obj E' X.property hY
  obtain ⟨e, -⟩ := counit_iso (⟨X.obj.baseChange (E' : Type u), hY⟩ : SplitSpecies (E' : Type u) L)
  exact ⟨((toSpeciesFunctor (E' : Type u) L).mapIso
    (asIso (EtaleSpecies.bcQuiverHom X.obj E' X.property hY))).unop ≪≫ e.symm⟩

/-- The transported restriction **is** the restriction of `RQ2-2.07`, on objects.

Proof plan (G4): the same computation for `Gal(L/K) ×_{Gal(L/E')} (−)`, whose orbits are the
`Gal(L/K)`-orbits of the induced set; `RQ2-2.07` is restriction of scalars, which on the quiver side
is exactly induction of the Galois action.

@census none (clause witness for `RQ2-2.08-C1`)
-/
theorem speciesRestriction_obj_iso (Y : SplitSpecies (E' : Type u) L) :
    Nonempty (((speciesRestriction K L E').obj Y).obj ≅ EtaleSpecies.restriction (K := K) Y.obj) := by
  rw [speciesRestriction, (speciesEquiv_functor_inverse (E' : Type u) L).2,
    (speciesEquiv_functor_inverse K L).1]
  haveI := RestrictionIso.restrictionQuiverHom_isIso E' Y.obj Y.property
  obtain ⟨e, -⟩ := counit_iso
    (⟨EtaleSpecies.restriction (K := K) Y.obj,
      RestrictionIso.restriction_isSplitBy E' Y.obj Y.property⟩ : SplitSpecies K L)
  exact ⟨(((toSpeciesFunctor K L).mapIso
    (asIso (RestrictionIso.restrictionQuiverHom E' Y.obj Y.property))).unop).symm ≪≫ e.symm⟩

/-- **Proposition 2.8** (`prop:speciesrestrictionbasechangeadjunction`, census `RQ2-2.08`).
For a finite separable extension `E'/K`, any étale `K`-species `S` and any étale `E'`-species `S'`,
there is a natural isomorphism

`Hom_{E'}(S ⊗_K E', S') ≅ Hom_K(S, res_{E'/K} S')`,

i.e. base change is left adjoint to restriction. Naturality in both variables is not an extra
conjunct here: it is what `CategoryTheory.Adjunction` *is* (unit/counit data satisfying the
triangle identities), exactly as for the quiver-side `RQ2-1.07`.

@census    RQ2-2.08
@source    prop:speciesrestrictionbasechangeadjunction
@clauses   RQ2-2.08-H1, RQ2-2.08-H2, RQ2-2.08-H3, RQ2-2.08-C1, RQ2-2.08-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION on clause `RQ2-2.08-H1`. The source quantifies over *any* finite
separable extension `N/K`; we quantify over an intermediate field `E'` of a fixed finite Galois
`L/K` with `E'/K` finite — which is the same generality, since every finite separable `N/K`
embeds into a finite Galois `L/K` (and the anti-equivalence of `RQ2-2.13`, on which this proof
rests, fixes such an `L` anyway: clause `RQ2-2.13-H1`, which the census itself marks a
`JUSTIFIED_REFORMULATION`). This is the shape stage S1 gave the quiver-side `RQ2-1.07`, whose proof
this one transports. Clauses `H2` and `H3` — "for any étale `K`-species `S`", "for any étale
`N`-species `S'`" — are the universal quantification built into an `Adjunction`, whose `homEquiv`
ranges over all objects of both categories, as for `RQ2-1.07`. `C1` and `C2` are the `Adjunction`
itself: the displayed isomorphism is `Adjunction.homEquiv` and its naturality is structural.

**Clause `C1`'s witnesses, named (verification finding C-3).** What makes the two functors of this
adjunction the *source's* base change and restriction — and not merely some transported pair — is
the agreement pair `speciesBaseChange_obj_iso` and `speciesRestriction_obj_iso`, which identify them
with `RQ2-2.05`'s `EtaleSpecies.baseChange` and `RQ2-2.07`'s `EtaleSpecies.restriction`. Both are
**object-level** statements, which is the maximum available today because stage S3 landed base
change on objects only; when base change on morphisms exists the agreement must be upgraded to a
natural isomorphism of functors, and that upgrade is a G4/G6 obligation recorded here and in
`workflow/stages/S4/DESIGN-NOTES.md` §7.2.
**Carried obligation O-1 DISCHARGED 2026-09-02** (commission C-M1-1, `WORKFLOW.md` F5 amendment of
frozen S4; `workflow/ledger/OBLIGATIONS.md`). That upgrade has landed: `baseChangeFunctor` and
`restrictionFunctor` extend `RQ2-2.05`'s base change and `RQ2-2.07`'s restriction to **functors** on
`SplitSpecies` whose object maps are those constructions *definitionally*
(`baseChangeFunctor_obj`, `restrictionFunctor_obj` are `rfl`), the agreement is now the natural
isomorphism of functors `speciesBaseChange_natIso`/`speciesRestriction_natIso`, and
`restriction_baseChange_adjunction_functorial` carries this adjunction onto them. The two
object-level statements above are **unchanged** and are exactly what the upgrade consumes.
Disclosed residual: those morphism maps are obtained by transport along chosen object isomorphisms
(`Nonempty.some`, hence `Classical.choice`), not by the intrinsic `piIndexOf` construction
`DESIGN-NOTES.md` §7.2 costed; the hand-over is written at `baseChangeFunctor`.
The statement asserts that such an adjunction **exists**; the source likewise asserts that a
natural isomorphism exists, and does not name it.

Proof plan (G4), the source's own: `RQ2-1.07` gives `restriction ⊣ baseChange` on quivers as real
data (stage S1, `RationalQuiver.restriction_baseChange_adjunction`). Transport it along the two
anti-equivalences `speciesEquiv K L` and `speciesEquiv E' L`: an adjunction transported along
equivalences stays an adjunction (`Adjunction.ofNatIsoLeft`/`Right`, `Equivalence.toAdjunction`,
`Adjunction.comp`), and passing to opposite categories exchanges left and right adjoints — which is
why restriction ⊣ base change on quivers becomes **base change ⊣ restriction** on species, the
direction the source's `eq:restrictionadjunction` displays. Since the two species-side functors are
*defined* as those transports, the transport is definitional and the only real content is the pair
of agreement theorems above.
-/
theorem restriction_baseChange_adjunction :
    Nonempty (speciesBaseChange K L E' ⊣ speciesRestriction K L E') :=
  ⟨Adjunction.unop
    (((speciesEquiv (E' : Type u) L).symm.toAdjunction.comp
      (RationalQuiver.restriction_baseChange_adjunction K L E')).comp
      (speciesEquiv K L).toAdjunction)⟩

/-! ## Carried obligation **O-1**, discharged: the `RQ2-2.08-C1` agreement upgraded to a natural
isomorphism of functors

**The booking** (`workflow/ledger/OBLIGATIONS.md` row `O-1`, from S4 `G4-VERIFICATION.md` §8.2 and
`stages/S4/FREEZE.md` §4.3): *`RQ2-2.08-C1`'s agreement with `RQ2-2.05`/`RQ2-2.07` is object-level only
(`speciesBaseChange_obj_iso`/`speciesRestriction_obj_iso` are `Nonempty (obj ≅ obj)`); when
`EtaleSpecies.baseChange` acquires a morphism-level (functorial) extension, the agreement theorems
must be upgraded to a natural isomorphism of functors.*  Discharged by commission **C-M1-1**,
2026-09-02, as a dated `WORKFLOW.md` F5 amendment of frozen stage S4.

**What is delivered.**  `EtaleSpecies.baseChange` and `EtaleSpecies.restriction` acquire
morphism-level extensions on the subcategory `SplitSpecies` where `RQ2-2.08` lives —
`baseChangeFunctor` and `restrictionFunctor` — whose **object maps are literally**
`X ↦ X.obj.baseChange E'` and `Y ↦ EtaleSpecies.restriction Y.obj`
(`baseChangeFunctor_obj`/`restrictionFunctor_obj` are `rfl`).  The agreement is then a **natural
isomorphism of functors**, `speciesBaseChange_natIso` and `speciesRestriction_natIso`, replacing
the per-object `Nonempty (… ≅ …)`; and `restriction_baseChange_adjunction_functorial` transports
`RQ2-2.08`'s adjunction onto the pair, so the displayed isomorphism
`Hom_{E'}(S ⊗_K E', S') ≅ Hom_K(S, res S')` now holds with the source's own base change and
restriction as the two functors, not merely with functors object-wise isomorphic to them.

Two named `def`s (`speciesBaseChangeObjIso`, `speciesRestrictionObjIso`) turn the frozen
`Nonempty` statements into the objects the construction consumes — the `PROCESS-CHANGELOG.md`
2026-08-30 pattern "∃ for the gate, named def for the consumers"; the frozen statements themselves
are untouched.  The functor is mathlib's `CategoryTheory.Functor.copyObj` with its
`Functor.isoCopyObj`, not a private restatement (R2).

**Disclosed residual, and the hand-over.**  The morphism map of `baseChangeFunctor` is obtained by
*transport* along the chosen object isomorphisms, so it is canonical only up to those choices
(`Nonempty.some`, hence `Classical.choice`, which is a sanctioned axiom).  What this does **not**
deliver is the intrinsic construction S4's `DESIGN-NOTES.md` §7.2 costed — base change on morphisms
built from `eq:speciesvertexdecomposition` directly, which needs a `piIndexOf` datum mathlib lacks
(`ledger/MATHLIB-DECISIONS.tsv` `MD-S3-09`) plus an API layer over S3's `baseChangeEdge` the size
of that construction.  **Handed over, not booked as a new obligation**: should a later stage build
that intrinsic map, the statement it owes is that it is naturally isomorphic to
`baseChangeFunctor` over the identity of the object map — which, both being extensions of the same
object map, is exactly the uniqueness question S4 §7.2 left open.  No consumer in M1 needs it: every
M1 use of `RQ2-2.08` is through the adjunction, which is now available on the source's own functors.
-/

section ObligationO1

/-- Base change of `RQ2-2.05` as a map on `L`-split species, with the splitting proof attached.
The object half of `baseChangeFunctor`.

@census none (helper: carried obligation O-1)
-/
noncomputable def baseChangeSplitObj (X : SplitSpecies K L) : SplitSpecies (E' : Type u) L :=
  ⟨X.obj.baseChange (E' : Type u), X.obj.baseChange_isSplitBy (E' : Type u) X.property⟩

/-- The **chosen** object-level agreement isomorphism of `RQ2-2.08-C1`, as data.  Frozen
`speciesBaseChange_obj_iso` asserts `Nonempty (…)`; this names one, in the subcategory (the
inclusion `ObjectProperty.ι` is fully faithful, so an ambient iso between two split species is an
iso of split species).

@census none (helper: carried obligation O-1; "∃ for the gate, named def for the consumers")
-/
noncomputable def speciesBaseChangeObjIso (X : SplitSpecies K L) :
    (speciesBaseChange K L E').obj X ≅ baseChangeSplitObj K L E' X :=
  (EtaleSpecies.splitBy (E' : Type u) L).ι.preimageIso (speciesBaseChange_obj_iso K L E' X).some

/-- **O-1, base-change half: `EtaleSpecies.baseChange` extended to a functor.**  Its object map is
`RQ2-2.05`'s base change on the nose (`baseChangeFunctor_obj`); its morphism map is the transport of
`speciesBaseChange`'s along `speciesBaseChangeObjIso`.

@census none (carried obligation O-1)
-/
noncomputable def baseChangeFunctor : SplitSpecies K L ⥤ SplitSpecies (E' : Type u) L :=
  (speciesBaseChange K L E').copyObj (baseChangeSplitObj K L E') (speciesBaseChangeObjIso K L E')

/-- The functor of `O-1` **is** `RQ2-2.05`'s base change on objects — definitionally, not up to
isomorphism.  This is what makes the natural isomorphism below an agreement statement about the
source's own construction.

@census none (carried obligation O-1)
-/
theorem baseChangeFunctor_obj (X : SplitSpecies K L) :
    ((baseChangeFunctor K L E').obj X).obj = X.obj.baseChange (E' : Type u) := rfl

/-- **O-1, base-change half, discharged**: the agreement of `RQ2-2.08-C1` with `RQ2-2.05`, upgraded
from a per-object `Nonempty (… ≅ …)` to a **natural isomorphism of functors**.

@census none (carried obligation O-1)
-/
noncomputable def speciesBaseChange_natIso :
    speciesBaseChange K L E' ≅ baseChangeFunctor K L E' :=
  (speciesBaseChange K L E').isoCopyObj _ _

/-- Restriction of `RQ2-2.07` as a map on `L`-split species, with the splitting proof attached.

@census none (helper: carried obligation O-1)
-/
noncomputable def restrictionSplitObj (Y : SplitSpecies (E' : Type u) L) : SplitSpecies K L :=
  ⟨EtaleSpecies.restriction (K := K) Y.obj,
    RestrictionIso.restriction_isSplitBy E' Y.obj Y.property⟩

/-- The **chosen** object-level agreement isomorphism of `RQ2-2.08-C1`, restriction half.

@census none (helper: carried obligation O-1)
-/
noncomputable def speciesRestrictionObjIso (Y : SplitSpecies (E' : Type u) L) :
    (speciesRestriction K L E').obj Y ≅ restrictionSplitObj K L E' Y :=
  (EtaleSpecies.splitBy K L).ι.preimageIso (speciesRestriction_obj_iso K L E' Y).some

/-- **O-1, restriction half: `EtaleSpecies.restriction` extended to a functor.**

@census none (carried obligation O-1)
-/
noncomputable def restrictionFunctor : SplitSpecies (E' : Type u) L ⥤ SplitSpecies K L :=
  (speciesRestriction K L E').copyObj (restrictionSplitObj K L E') (speciesRestrictionObjIso K L E')

/-- The functor of `O-1` **is** `RQ2-2.07`'s restriction on objects, definitionally.

@census none (carried obligation O-1)
-/
theorem restrictionFunctor_obj (Y : SplitSpecies (E' : Type u) L) :
    ((restrictionFunctor K L E').obj Y).obj = EtaleSpecies.restriction (K := K) Y.obj := rfl

/-- **O-1, restriction half, discharged**: the agreement of `RQ2-2.08-C1` with `RQ2-2.07`, as a
natural isomorphism of functors.

@census none (carried obligation O-1)
-/
noncomputable def speciesRestriction_natIso :
    speciesRestriction K L E' ≅ restrictionFunctor K L E' :=
  (speciesRestriction K L E').isoCopyObj _ _

/-- **O-1, the payoff.**  `RQ2-2.08`'s adjunction, transported onto the two functors whose object
maps are `RQ2-2.05`'s base change and `RQ2-2.07`'s restriction themselves.  The frozen statement
`restriction_baseChange_adjunction` is unchanged and is what this consumes; this is the
functorial-agreement form the obligation asked for.

@census none (carried obligation O-1)
-/
theorem restriction_baseChange_adjunction_functorial :
    Nonempty (baseChangeFunctor K L E' ⊣ restrictionFunctor K L E') := by
  obtain ⟨adj⟩ := restriction_baseChange_adjunction K L E'
  exact ⟨Adjunction.ofNatIsoRight (Adjunction.ofNatIsoLeft adj (speciesBaseChange_natIso K L E'))
    (speciesRestriction_natIso K L E')⟩

end ObligationO1

end RationalQuivers
