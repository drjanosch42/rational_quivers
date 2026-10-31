module

public import RationalQuivers.Descent.Hom
public import RationalQuivers.Quiver.Basic

@[expose] public section

/-!
# Rational quiver representations

Formalizes the first half of §1.3 of `latex/rational_quivers.tex`
(census `RQ2-1.08`, `RQ2-1.09`).

## Main definitions / results
* `RationalQuivers.RationalQuiver.Rep` — Definition `def:rationalrepresentations`
  (census `RQ2-1.08`): a family of `L`-vector spaces `M(v)`, semi-linear isomorphisms
  `φ_{v,σ} : M(v) → M(σ v)` satisfying the cocycle condition and acting **continuously on the
  disjoint union** `⊔_v M(v)`, and `L`-linear edge maps `φ_e` compatible with the Galois action.
* `RationalQuivers.RationalQuiver.Rep.Total` — the disjoint union `⊔_{v ∈ V} M(v)`, with the
  `Gal(L/K)`-action of `def:rationalrepresentations`(ii); `Rep.isSmooth_total` and
  `Rep.continuousSMul_total` are the continuity clause `RQ2-1.08-C6`.
* `RationalQuivers.RationalQuiver.Rep.Hom` — Definition `def:rationalrepresentationhom`
  (census `RQ2-1.09`).
* `RationalQuivers.RationalQuiver.Rep.constL` — the non-degenerate inhabitant (G5).

## Implementation notes

**The dependent-type crux, and why no `cast` occurs in a statement.**  `φ_{v,σ}` goes
`M(v) → M(σ v)`, so the cocycle condition `φ_{τv,σ} ∘ φ_{v,τ} = φ_{v,στ}`
(`eq:semi-linearactiononrep`) and the edge condition
`φ_{σe} ∘ φ_{s(e),σ} = φ_{t(e),σ} ∘ φ_e` (`eq:koecheractiononrep`) each compare two maps whose
codomains are only *propositionally* equal: `σ • (τ • v) = (σ * τ) • v` and
`Γ.source (σ • e) = σ • Γ.source e` are lemmas, not definitional equalities
(`mul_smul`, `RationalQuiver.source_smul`).  A formalization that transports along them with
`Eq.mpr`/`▸` inside the *statement* is the shape `stages/S2/PLAN.md` §6 names as the archetypal
`WEAKENED_OR_PARTIAL` risk.

We avoid it exactly as the source does: the paper itself reads the semi-linear maps as an action
on the **disjoint union** `⊔_v M(v)`.  Both conditions are therefore stated as equalities of
elements of the sigma type `Total = (v : Γ.V) × M v`, where the two "different" vertices are
compared inside the equation rather than by transporting the fibres.  This is literally
`eq:semi-linearactiononrep` / `eq:koecheractiononrep` read in `⊔_v M(v)`, and it contains no
`cast`.  The paper-shaped readings, which do transport, are the derived lemmas `Rep.cocycle'`
and `Rep.edge_equivariance'`; `Rep.eqCast` is the transport they use, confined to helpers.

**Semi-linearity.**  Following S0 (`Descent.IsSemilinear`, ledger row `MD-S0-01`), a semi-linear
isomorphism is carried as a bundled *additive* equivalence `M v ≃+ M (σ • v)` (clauses
`RQ2-1.08-C2`, `RQ2-1.08-C3`) together with the `Prop`-valued semi-linearity axiom (clause
`RQ2-1.08-C4`); `Rep.isSemilinear_φ` records that this is S0's predicate and
`Rep.toSemilinearMap_φ` the bridge to mathlib's bundled `→ₛₗ`.

**Standing hypothesis.**  `L/K` Galois is carried structurally: a `Rep` takes a
`RationalQuiver K L` argument, whose `galois` field (`RQ2-1.02-H1`) cannot be dropped
(`CONVENTIONS.md` §3, r6 delta).  As S1 records, the field is available as the term `Γ.galois`
and is *not* instance-synthesizable; proofs that need it write `haveI := Γ.galois`.
-/

universe u

namespace RationalQuivers

namespace RationalQuiver

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- **Definition** (`def:rationalrepresentations`, §1.3 of the source).

Let `Γ_K` be a quiver over `K` with respect to a Galois extension `L/K` (clause `RQ2-1.08-H1`,
the argument `Γ`).  A *(`K`-rational) representation* `M_K` of `Γ_K` consists of

* (i) a family `M = (M(v))_{v ∈ V}` of `L`-vector spaces (clause `RQ2-1.08-C1`);
* (ii) semi-linear isomorphisms `φ_{v,σ} : M(v) → M(σ v)` for each `v ∈ V` and
  `σ ∈ Gal(L/K)` (clauses `RQ2-1.08-C2`, `RQ2-1.08-C3`, `RQ2-1.08-C4`) satisfying the cocycle
  condition `φ_{τ v,σ} ∘ φ_{v,τ} = φ_{v,στ}` (`eq:semi-linearactiononrep`, clause
  `RQ2-1.08-C5`) and such that the resulting action of `Gal(L/K)` on the **disjoint union**
  `⊔_{v ∈ V} M(v)`, considered as a discrete set, is **continuous** (clause `RQ2-1.08-C6`);
* (iii) for each edge `e ∈ E` an `L`-linear map `φ_e : M(s(e)) → M(t(e))` (clause
  `RQ2-1.08-C8`) with `φ_{σ e} ∘ φ_{s(e),σ} = φ_{t(e),σ} ∘ φ_e` (`eq:koecheractiononrep`,
  clause `RQ2-1.08-C9`).

The continuity condition is automatic for finite `L/K` (clause `RQ2-1.08-C7`,
`Rep.ofFiniteDimensional`).  The continuity field is stated for points of the disjoint union
`Total`, *not* for each `M(v)` separately: that is what `census/NOTATION.md` §5 flags as
clause-critical about `RQ2-1.08-C6`.

@census    RQ2-1.08
@source    def:rationalrepresentations
@clauses   RQ2-1.08-H1, RQ2-1.08-C1, RQ2-1.08-C2, RQ2-1.08-C3, RQ2-1.08-C4, RQ2-1.08-C5,
           RQ2-1.08-C6, RQ2-1.08-C8, RQ2-1.08-C9
@imports   none
@divergence JUSTIFIED_REFORMULATION (verifier-agreed, `stages/S2/VERIFICATION.md` V-2).  The
cocycle and edge-equivariance clauses are stated as equalities in the
disjoint union `⊔_v M(v)` rather than by transporting fibres along `σ • (τ • v) = (σ*τ) • v`
resp. `s(σ e) = σ s(e)`; this is the same equation, read in the set on which the source itself
puts the action, and it keeps every `cast` out of the statement.  `Rep.cocycle'` and
`Rep.edge_equivariance'` prove the literally-transported readings, so nothing is lost.
-/
structure Rep (Γ : RationalQuiver K L) : Type (u + 1) where
  /-- Clause `RQ2-1.08-C1`: the family `M = (M(v))_{v ∈ V}` of `L`-vector spaces. -/
  M : Γ.V → Type u
  /-- Clause `RQ2-1.08-C1`: each `M(v)` is an abelian group. -/
  [addCommGroup : ∀ v, AddCommGroup (M v)]
  /-- Clause `RQ2-1.08-C1`: each `M(v)` is an `L`-vector space. -/
  [module : ∀ v, Module L (M v)]
  /-- Clauses `RQ2-1.08-C2`, `RQ2-1.08-C3`: for each `v` and `σ` an isomorphism
  `φ_{v,σ} : M(v) → M(σ v)`.  Bijectivity and additivity are the bundled `≃+`;
  `σ`-semi-linearity is the field `semilinear`. -/
  φ : ∀ (σ : Gal(L/K)) (v : Γ.V), M v ≃+ M (σ • v)
  /-- Clause `RQ2-1.08-C4`: `φ_{v,σ}(a · m) = σ(a) · φ_{v,σ}(m)`. -/
  semilinear : ∀ (σ : Gal(L/K)) (v : Γ.V) (a : L) (m : M v), φ σ v (a • m) = σ a • φ σ v m
  /-- Clause `RQ2-1.08-C5`, `eq:semi-linearactiononrep`: the cocycle condition
  `φ_{τ v,σ} ∘ φ_{v,τ} = φ_{v,στ}`, read as an equality in the disjoint union `⊔_v M(v)`.
  Note the source's index order: the composite is indexed `σ τ`. -/
  cocycle : ∀ (σ τ : Gal(L/K)) (v : Γ.V) (m : M v),
      (⟨σ • (τ • v), φ σ (τ • v) (φ τ v m)⟩ : (w : Γ.V) × M w) = ⟨(σ * τ) • v, φ (σ * τ) v m⟩
  /-- Clause `RQ2-1.08-C6`: the resulting action of `Gal(L/K)` on the disjoint union
  `⊔_{v ∈ V} M(v)`, considered as a **discrete set**, is continuous — in the open-stabilizer
  form prescribed by `census/NOTATION.md` §12.  The condition is imposed **jointly** on the
  vertex action and the semi-linear actions, not on each `M(v)` separately. -/
  smooth : ∀ x : (v : Γ.V) × M v,
      IsOpen {σ : Gal(L/K) | (⟨σ • x.1, φ σ x.1 x.2⟩ : (w : Γ.V) × M w) = x}
  /-- Clause `RQ2-1.08-C8`: for each edge `e` an `L`-linear map `φ_e : M(s(e)) → M(t(e))`. -/
  φEdge : ∀ e : Γ.E, M (Γ.toRQuiver.source e) →ₗ[L] M (Γ.toRQuiver.target e)
  /-- Clause `RQ2-1.08-C9`, `eq:koecheractiononrep`:
  `φ_{σ e} ∘ φ_{s(e),σ} = φ_{t(e),σ} ∘ φ_e`, read as an equality in the disjoint union
  `⊔_v M(v)`.  The hypothesis pins `m'` to be `φ_{s(e),σ}(m)` viewed in the fibre over
  `s(σ e) = σ s(e)`; `Rep.edge_equivariance'` is the transported, paper-shaped reading. -/
  edge_equivariance : ∀ (σ : Gal(L/K)) (e : Γ.E) (m : M (Γ.toRQuiver.source e))
      (m' : M (Γ.toRQuiver.source (σ • e))),
      (⟨Γ.toRQuiver.source (σ • e), m'⟩ : (w : Γ.V) × M w)
          = ⟨σ • Γ.toRQuiver.source e, φ σ (Γ.toRQuiver.source e) m⟩ →
      (⟨Γ.toRQuiver.target (σ • e), φEdge (σ • e) m'⟩ : (w : Γ.V) × M w)
          = ⟨σ • Γ.toRQuiver.target e, φ σ (Γ.toRQuiver.target e) (φEdge e m)⟩

attribute [instance] Rep.addCommGroup Rep.module

/-- Transport of a bare vertex-indexed family of `L`-vector spaces along an equality of vertices.
This is the only transport in the development; it is confined to helpers and to the paper-shaped
restatements `cocycle'`, `edge_equivariance'`, and never occurs in a census-carrying statement.

It is stated for a bare family, not for a `Rep`, so that a construction depending only on the
family (`Quiver/Rep/Nilpotent.lean`'s `pathCompose`) is literally the same term for a
representation and for its base change.

@census none (helper)
-/
def famCast {V : Type u} (X : V → Type u) [∀ v, AddCommGroup (X v)] [∀ v, Module L (X v)]
    {v w : V} (h : v = w) : X v ≃ₗ[L] X w := by
  subst h; exact LinearEquiv.refl L (X v)

namespace Rep

variable {Γ : RationalQuiver K L}

/-! ### The disjoint union `⊔_v M(v)` and its `Gal(L/K)`-action -/

/-- The disjoint union `⊔_{v ∈ V} M(v)` of `def:rationalrepresentations`(ii), the set on which
the source imposes continuity.

@census none (helper: the carrier of clause `RQ2-1.08-C6`)
-/
def Total (M : Rep Γ) : Type u := (v : Γ.V) × M.M v

/-- The point `(v, m)` of the disjoint union `⊔_v M(v)`.  A named constructor, so that the type
stays `M.Total` and the `MulAction` instance below is found by unification.

@census none (helper)
-/
def tot (M : Rep Γ) (v : Γ.V) (m : M.M v) : M.Total := ⟨v, m⟩

/-- The vertex of a point of the disjoint union.  @census none (helper) -/
@[simp]
theorem tot_fst (M : Rep Γ) (v : Γ.V) (m : M.M v) : (M.tot v m).1 = v := rfl


/-- `famCast` for the family underlying a representation.

@census none (helper)
-/
def eqCast (M : Rep Γ) {v w : Γ.V} (h : v = w) : M.M v ≃ₗ[L] M.M w := famCast M.M h

/-- Transport along `rfl` is the identity.  @census none (helper) -/
@[simp]
theorem eqCast_rfl (M : Rep Γ) (v : Γ.V) (m : M.M v) : M.eqCast (rfl : v = v) m = m := rfl

/-- Transport and its inverse cancel.  @census none (helper) -/
@[simp]
theorem eqCast_symm_apply (M : Rep Γ) {v w : Γ.V} (h : v = w) (m : M.M w) :
    M.eqCast h (M.eqCast h.symm m) = m := by subst h; rfl

/-- An equality in the disjoint union `⊔_v M(v)` between elements of known fibres is exactly an
equality of fibre elements after transport.  This is what makes the `Total`-shaped fields of `Rep`
interchangeable with the paper's transported readings.

@census none (helper)
-/
theorem sigma_mk_eq_iff (M : Rep Γ) {v w : Γ.V} (h : v = w) (m : M.M v) (m' : M.M w) :
    (⟨v, m⟩ : M.Total) = ⟨w, m'⟩ ↔ M.eqCast h m = m' := by
  subst h
  simp [Sigma.mk.injEq]

/-- `sigma_mk_eq_iff` for the named constructor `tot`.  @census none (helper) -/
theorem tot_eq_iff (M : Rep Γ) {v w : Γ.V} (h : v = w) (m : M.M v) (m' : M.M w) :
    M.tot v m = M.tot w m' ↔ M.eqCast h m = m' := M.sigma_mk_eq_iff h m m'

/-- Clause `RQ2-1.08-C5` in the paper's transported form:
`φ_{τ v,σ} ∘ φ_{v,τ} = φ_{v,στ}` as maps `M(v) → M(σ τ v)`.

@census none (helper: the paper-shaped reading of clause `RQ2-1.08-C5`)
-/
theorem cocycle' (M : Rep Γ) (σ τ : Gal(L/K)) (v : Γ.V) (m : M.M v) :
    M.eqCast (mul_smul σ τ v) (M.φ (σ * τ) v m) = M.φ σ (τ • v) (M.φ τ v m) := by
  have h2 := (M.sigma_mk_eq_iff (mul_smul σ τ v).symm _ _).1 (M.cocycle σ τ v m)
  rw [← h2, eqCast_symm_apply]

/-- Clause `RQ2-1.08-C9` in the paper's transported form:
`φ_{σ e} ∘ φ_{s(e),σ} = φ_{t(e),σ} ∘ φ_e` as maps `M(s(e)) → M(σ t(e))`.

@census none (helper: the paper-shaped reading of clause `RQ2-1.08-C9`)
-/
theorem edge_equivariance' (M : Rep Γ) (σ : Gal(L/K)) (e : Γ.E)
    (m : M.M (Γ.toRQuiver.source e)) :
    haveI := Γ.galois
    M.eqCast (Γ.target_smul σ e)
        (M.φEdge (σ • e)
          (M.eqCast (Γ.source_smul σ e).symm (M.φ σ (Γ.toRQuiver.source e) m)))
      = M.φ σ (Γ.toRQuiver.target e) (M.φEdge e m) := by
  haveI := Γ.galois
  refine (M.sigma_mk_eq_iff (Γ.target_smul σ e) _ _).1 (M.edge_equivariance σ e m _ ?_)
  exact (M.sigma_mk_eq_iff (Γ.source_smul σ e) _ _).2 (by simp)

/-! ### Semi-linearity: the bridge to S0 -/

/-- Clause `RQ2-1.08-C4` in S0's vocabulary: each `φ_{v,σ}` is `σ`-linear in the sense of
`Descent.IsSemilinear` (census `RQ2-1.15`).

@census none (helper: clause `RQ2-1.08-C4`)
-/
theorem isSemilinear_φ (M : Rep Γ) (σ : Gal(L/K)) (v : Γ.V) :
    Descent.IsSemilinear σ (fun m : M.M v => M.φ σ v m) :=
  M.semilinear σ v

/-- Clause `RQ2-1.08-C4`, bridge to mathlib (`CONVENTIONS.md` §6 ladder step 1): `φ_{v,σ}` is a
bundled `σ`-semi-linear map `M(v) →ₛₗ[σ] M(σ v)`.

@census none (helper: clause `RQ2-1.08-C4`)
-/
def toSemilinearMap_φ (M : Rep Γ) (σ : Gal(L/K)) (v : Γ.V) :
    M.M v →ₛₗ[(σ.toRingEquiv.toRingHom : L →+* L)] M.M (σ • v) :=
  Descent.toSemilinearMap σ (M.φ σ v).toAddMonoidHom (M.isSemilinear_φ σ v)

/-! ### The action on the disjoint union -/

/-- `φ_{v,1} = id`, read in the disjoint union: a consequence of the cocycle condition
(clause `RQ2-1.08-C5`) and the bijectivity of the `φ_{v,σ}` (clause `RQ2-1.08-C3`).

@census none (helper)
-/
theorem smul_one_total (M : Rep Γ) (x : M.Total) :
    (⟨(1 : Gal(L/K)) • x.1, M.φ 1 x.1 x.2⟩ : M.Total) = x := by
  have hinj : Function.Injective
      (fun y : M.Total => (⟨(1 : Gal(L/K)) • y.1, M.φ 1 y.1 y.2⟩ : M.Total)) := by
    rintro ⟨v, m⟩ ⟨w, n⟩ h
    have h1 : (1 : Gal(L/K)) • v = (1 : Gal(L/K)) • w :=
      congrArg (fun y : M.Total => y.1) h
    have hvw : v = w := by simpa using h1
    subst hvw
    have h2 : M.φ 1 v m = M.φ 1 v n := by
      simpa using (M.sigma_mk_eq_iff
        (rfl : (1 : Gal(L/K)) • v = (1 : Gal(L/K)) • v) _ _).1 h
    have := (M.φ 1 v).injective h2
    subst this
    rfl
  refine hinj ?_
  obtain ⟨v, m⟩ := x
  have h := M.cocycle 1 1 v m
  rw [one_mul] at h
  exact h

/-- The action of `Gal(L/K)` on the disjoint union `⊔_v M(v)`, `σ · (v, m) = (σ v, φ_{v,σ} m)`.
That this is a group action is exactly the cocycle condition `eq:semi-linearactiononrep`
(clause `RQ2-1.08-C5`).

@census none (helper: the action of clause `RQ2-1.08-C6`)
-/
instance mulActionTotal (M : Rep Γ) : MulAction Gal(L/K) M.Total where
  smul σ x := ⟨σ • x.1, M.φ σ x.1 x.2⟩
  one_smul := M.smul_one_total
  mul_smul σ τ x := (M.cocycle σ τ x.1 x.2).symm

/-- The action on the disjoint union, in components.  @census none (helper) -/
@[simp]
theorem smul_total_def (M : Rep Γ) (σ : Gal(L/K)) (x : M.Total) :
    σ • x = (⟨σ • x.1, M.φ σ x.1 x.2⟩ : M.Total) := rfl

/-! ### The transported structure maps `φ'` -/

/-- `σ (σ⁻¹ a) = a` for `σ ∈ Gal(L/K)`.  @census none (helper) -/
theorem apply_inv_apply (σ : Gal(L/K)) (a : L) : σ (σ⁻¹ a) = a := by
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

/-- The structure map `φ_{v,σ}` **transported to a named target vertex**: given a proof that
`σ • v = w`, `φ' σ h : M(v) ≃+ M(w)`.

Every use of `Rep.eqCast` in the development is packaged here.  The payoff is
`Rep.φ'_comp`: the cocycle condition holds for `φ'` in *one* form that covers every way the three
vertices can be presented, because Lean's proof irrelevance makes `eqCast h` depend only on the
*statement* of `h`.  Without it each transported composition needs its own `subst` bookkeeping.

@census none (helper: the transported form of clauses `RQ2-1.08-C2`–`C5`)
-/
def φ' (M : Rep Γ) (σ : Gal(L/K)) {v w : Γ.V} (h : σ • v = w) : M.M v ≃+ M.M w :=
  (M.φ σ v).trans (M.eqCast h).toAddEquiv

/-- `φ'` in terms of `φ` and the transport.  @census none (helper) -/
@[simp]
theorem φ'_apply (M : Rep Γ) (σ : Gal(L/K)) {v w : Γ.V} (h : σ • v = w) (m : M.M v) :
    M.φ' σ h m = M.eqCast h (M.φ σ v m) := rfl

/-- With no transport, `φ'` is `φ`.  @census none (helper) -/
theorem φ'_rfl (M : Rep Γ) (σ : Gal(L/K)) (v : Γ.V) (m : M.M v) :
    M.φ' σ (rfl : σ • v = σ • v) m = M.φ σ v m := rfl

/-- Clause `RQ2-1.08-C4` for `φ'`: `φ'` is `σ`-semi-linear.  @census none (helper) -/
theorem φ'_smul (M : Rep Γ) (σ : Gal(L/K)) {v w : Γ.V} (h : σ • v = w) (a : L) (m : M.M v) :
    M.φ' σ h (a • m) = σ a • M.φ' σ h m := by
  simp only [φ'_apply, M.semilinear σ v a m, map_smul]

/-- **Clause `RQ2-1.08-C5` in its most usable form.**  For any three vertices and any proofs that
`τ • v = w`, `σ • w = x` and `(σ τ) • v = x`, the cocycle condition
`φ_{τ v,σ} ∘ φ_{v,τ} = φ_{v,στ}` holds after transport.

@census none (helper: clause `RQ2-1.08-C5`)
-/
theorem φ'_comp (M : Rep Γ) (σ τ : Gal(L/K)) {v w x : Γ.V} (h₁ : τ • v = w) (h₂ : σ • w = x)
    (h₃ : (σ * τ) • v = x) (m : M.M v) :
    M.φ' σ h₂ (M.φ' τ h₁ m) = M.φ' (σ * τ) h₃ m := by
  subst h₁
  subst h₂
  simpa using (M.cocycle' σ τ v m).symm

/-- Clause `RQ2-1.08-C5` at `σ = 1`: `φ_{v,1}` is the identity, transported.

@census none (helper: clause `RQ2-1.08-C5`)
-/
theorem φ'_one (M : Rep Γ) {v w : Γ.V} (h : (1 : Gal(L/K)) • v = w) (m : M.M v) :
    M.φ' 1 h m = M.eqCast ((one_smul (Gal(L/K)) v).symm.trans h) m := by
  have h0 : (1 : Gal(L/K)) • v = v := one_smul _ v
  have key : M.eqCast h0.symm m = M.φ 1 v m :=
    (M.sigma_mk_eq_iff h0.symm m (M.φ 1 v m)).1 (M.smul_one_total ⟨v, m⟩).symm
  subst h
  exact key.symm

/-- `φ'` depends on the group element only through its value.  @census none (helper) -/
theorem φ'_congr (M : Rep Γ) {σ σ' : Gal(L/K)} (hσ : σ = σ') {v w : Γ.V}
    (h : σ • v = w) (h' : σ' • v = w) (m : M.M v) : M.φ' σ h m = M.φ' σ' h' m := by
  subst hσ; rfl

/-- The two transported structure maps of `σ` and `σ⁻¹` are mutually inverse.

@census none (helper: clause `RQ2-1.08-C3`)
-/
theorem φ'_inv (M : Rep Γ) (σ : Gal(L/K)) {v w : Γ.V} (h : σ • v = w)
    (h' : σ⁻¹ • w = v) (m : M.M v) : M.φ' σ⁻¹ h' (M.φ' σ h m) = m := by
  have hmul : (σ⁻¹ * σ) • v = v := by rw [inv_mul_cancel, one_smul]
  rw [M.φ'_comp σ⁻¹ σ h h' hmul,
    M.φ'_congr (inv_mul_cancel σ) hmul (one_smul (Gal(L/K)) v) m, M.φ'_one]
  exact M.eqCast_rfl v m

/-- The two transported structure maps of `σ` and `σ⁻¹` are mutually inverse (other order).

@census none (helper: clause `RQ2-1.08-C3`)
-/
theorem φ'_inv' (M : Rep Γ) (σ : Gal(L/K)) {v w : Γ.V} (h : σ⁻¹ • v = w)
    (h' : σ • w = v) (m : M.M v) : M.φ' σ h' (M.φ' σ⁻¹ h m) = m := by
  have hmul : (σ * σ⁻¹) • v = v := by rw [mul_inv_cancel, one_smul]
  rw [M.φ'_comp σ σ⁻¹ h h' hmul,
    M.φ'_congr (mul_inv_cancel σ) hmul (one_smul (Gal(L/K)) v) m, M.φ'_one]
  exact M.eqCast_rfl v m

/-- A vertex-indexed family of maps commutes with transport.  @census none (helper) -/
theorem eqCast_natural {M N : Rep Γ} (ψ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v) {v w : Γ.V}
    (h : v = w) (m : M.M v) : ψ w (M.eqCast h m) = N.eqCast h (ψ v m) := by
  subst h; rfl

/-! ### The transported edge maps `φEdge'` -/

/-- The edge map `φ_e` **transported to named endpoints**: given proofs that `s(e) = a` and
`t(e) = b`, `φEdge' e ha hb : M(a) → M(b)`.

@census none (helper: the transported form of clauses `RQ2-1.08-C8`, `RQ2-1.08-C9`)
-/
def φEdge' (M : Rep Γ) (e : Γ.E) {a b : Γ.V} (ha : Γ.toRQuiver.source e = a)
    (hb : Γ.toRQuiver.target e = b) : M.M a →ₗ[L] M.M b :=
  (M.eqCast hb).toLinearMap ∘ₗ M.φEdge e ∘ₗ (M.eqCast ha).symm.toLinearMap

/-- With no transport, `φEdge'` is `φEdge`.  @census none (helper) -/
theorem φEdge'_rfl (M : Rep Γ) (e : Γ.E) (m : M.M (Γ.toRQuiver.source e)) :
    M.φEdge' e rfl rfl m = M.φEdge e m := rfl

/-- **Clause `RQ2-1.08-C9` in its most usable form.**  `φ_{σ f} ∘ φ_{s(f),σ} = φ_{t(f),σ} ∘ φ_f`,
for any presentation of the four vertices and of the edge `σ f` involved.

@census none (helper: clause `RQ2-1.08-C9`)
-/
theorem φEdge'_φ' (M : Rep Γ) (σ : Gal(L/K)) {f e : Γ.E} (he : σ • f = e)
    {a b a' b' : Γ.V}
    (ha : Γ.toRQuiver.source f = a) (hb : Γ.toRQuiver.target f = b)
    (ha' : Γ.toRQuiver.source e = a') (hb' : Γ.toRQuiver.target e = b')
    (h₁ : σ • a = a') (h₂ : σ • b = b') (m : M.M a) :
    M.φEdge' e ha' hb' (M.φ' σ h₁ m) = M.φ' σ h₂ (M.φEdge' f ha hb m) := by
  haveI := Γ.galois
  subst he; subst ha; subst hb; subst ha'; subst hb'
  show M.φEdge (σ • f) (M.eqCast h₁ (M.φ σ (Γ.toRQuiver.source f) m))
      = M.eqCast h₂ (M.φ σ (Γ.toRQuiver.target f) (M.φEdge f m))
  have key := M.edge_equivariance' σ f m
  rw [← key, eqCast_symm_apply]

/-- The action on the disjoint union, through the named constructor.  @census none (helper) -/
@[simp]
theorem smul_tot (M : Rep Γ) (σ : Gal(L/K)) (v : Γ.V) (m : M.M v) :
    σ • M.tot v m = M.tot (σ • v) (M.φ σ v m) := rfl

/-- Clause `RQ2-1.08-C6`, open-stabilizer form: every point of the disjoint union `⊔_v M(v)` has
open stabilizer in `Gal(L/K)`.

@census none (helper: clause `RQ2-1.08-C6`)
-/
theorem isOpen_stabilizer_total (M : Rep Γ) (x : M.Total) :
    IsOpen (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) :=
  M.smooth x

/-- Clause `RQ2-1.08-C6` in the form S1 uses for `def:rationalquivers`: the induced permutation
action of `Gal(L/K)` on the discrete set `⊔_v M(v)` is smooth.

@census none (helper: clause `RQ2-1.08-C6`)
-/
theorem isSmooth_total (M : Rep Γ) : IsSmooth (MulAction.toPermHom Gal(L/K) M.Total) :=
  M.smooth

/-- Clause `RQ2-1.08-C6` as mathlib's `ContinuousSMul`: the action of `Gal(L/K)` on the disjoint
union `⊔_v M(v)`, considered as a **discrete** set, is continuous.  This is the literal reading of
the source's condition, and it is what makes clause `RQ2-1.08-C6` *mathlib's* notion of continuity
rather than a private restatement (`WORKFLOW.md` R2).

@census none (helper: clause `RQ2-1.08-C6`)
-/
theorem continuousSMul_total (M : Rep Γ) [TopologicalSpace M.Total] [DiscreteTopology M.Total] :
    ContinuousSMul Gal(L/K) M.Total :=
  continuousSMul_iff_stabilizer_isOpen.2 M.isOpen_stabilizer_total

/-- Clause `RQ2-1.08-C7`: for a **finite** extension `L/K` the continuity condition of
`def:rationalrepresentations`(ii) is automatic, `Gal(L/K)` then being discrete.  This constructor
builds a representation from the data (i), (ii), (iii) alone.

@census    none (auxiliary; discharges clause `RQ2-1.08-C7` of `RQ2-1.08`)
@source    def:rationalrepresentations
@clauses   RQ2-1.08-C7
@imports   none
@divergence none
-/
def ofFiniteDimensional [FiniteDimensional K L] {Γ : RationalQuiver K L} (M : Γ.V → Type u)
    [inst₁ : ∀ v, AddCommGroup (M v)] [inst₂ : ∀ v, Module L (M v)]
    (φ : ∀ (σ : Gal(L/K)) (v : Γ.V), M v ≃+ M (σ • v))
    (semilinear : ∀ (σ : Gal(L/K)) (v : Γ.V) (a : L) (m : M v), φ σ v (a • m) = σ a • φ σ v m)
    (cocycle : ∀ (σ τ : Gal(L/K)) (v : Γ.V) (m : M v),
      (⟨σ • (τ • v), φ σ (τ • v) (φ τ v m)⟩ : (w : Γ.V) × M w) = ⟨(σ * τ) • v, φ (σ * τ) v m⟩)
    (φEdge : ∀ e : Γ.E, M (Γ.toRQuiver.source e) →ₗ[L] M (Γ.toRQuiver.target e))
    (edge_equivariance : ∀ (σ : Gal(L/K)) (e : Γ.E) (m : M (Γ.toRQuiver.source e))
      (m' : M (Γ.toRQuiver.source (σ • e))),
      (⟨Γ.toRQuiver.source (σ • e), m'⟩ : (w : Γ.V) × M w)
          = ⟨σ • Γ.toRQuiver.source e, φ σ (Γ.toRQuiver.source e) m⟩ →
      (⟨Γ.toRQuiver.target (σ • e), φEdge (σ • e) m'⟩ : (w : Γ.V) × M w)
          = ⟨σ • Γ.toRQuiver.target e, φ σ (Γ.toRQuiver.target e) (φEdge e m)⟩) :
    Rep Γ where
  M := M
  φ := φ
  semilinear := semilinear
  cocycle := cocycle
  smooth _ := isOpen_discrete _
  φEdge := φEdge
  edge_equivariance := edge_equivariance

/-! ### Homomorphisms of rational representations -/

/-- **Definition** (`def:rationalrepresentationhom`, §1.3 of the source).

A *homomorphism* of `K`-rational representations `M = (M(v))_v`, `N = (N(v))_v` of `Γ_K`
(clause `RQ2-1.09-H1`, the two arguments) is a classical homomorphism
`(ψ_v : M(v) → N(v))_v` over `L` — i.e. an `L`-linear family commuting with the edge maps
(clause `RQ2-1.09-C1`) — which is compatible with the rational structures on `M` and `N`: for all
`v ∈ V` and all `σ ∈ Gal(L/K)` (clause `RQ2-1.09-H2`),

`ψ_{σ v} ∘ φ^M_{v,σ} = φ^N_{v,σ} ∘ ψ_v`   (`eq:koecheractiononrephom`, clause `RQ2-1.09-C2`).

As printed, `eq:koecheractiononrephom` omits the `M`/`N` superscripts and is ill-typed; the
census supplies them (ATTESTATION **AN-3**), and that is the reading formalized here.

@census    RQ2-1.09
@source    def:rationalrepresentationhom
@clauses   RQ2-1.09-H1, RQ2-1.09-H2, RQ2-1.09-C1, RQ2-1.09-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION (verifier-agreed, `stages/S2/VERIFICATION.md` V-2).  Both
conditions are stated cast-free: `ψ_{σ v} ∘ φ^M_{v,σ}` and
`φ^N_{v,σ} ∘ ψ_v` both land in `N(σ v)`, and `ψ_{t(e)} ∘ φ^M_e`, `φ^N_e ∘ ψ_{s(e)}` both land in
`N(t(e))`, so no transport is needed anywhere in this definition.
-/
@[ext]
structure Hom {Γ : RationalQuiver K L} (M N : Rep Γ) : Type u where
  /-- Clause `RQ2-1.09-C1`, first half: an `L`-linear map `ψ_v : M(v) → N(v)` for each vertex. -/
  ψ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v
  /-- Clause `RQ2-1.09-C1`, second half: `ψ` is a homomorphism of the underlying **classical**
  quiver representations over `L`, i.e. it commutes with the edge maps. -/
  edge : ∀ (e : Γ.E) (m : M.M (Γ.toRQuiver.source e)),
      ψ (Γ.toRQuiver.target e) (M.φEdge e m) = N.φEdge e (ψ (Γ.toRQuiver.source e) m)
  /-- Clause `RQ2-1.09-C2`, `eq:koecheractiononrephom` with the `M`/`N` superscripts supplied
  (ATTESTATION AN-3): `ψ_{σ v} ∘ φ^M_{v,σ} = φ^N_{v,σ} ∘ ψ_v`. -/
  rational : ∀ (σ : Gal(L/K)) (v : Γ.V) (m : M.M v),
      ψ (σ • v) (M.φ σ v m) = N.φ σ v (ψ v m)

namespace Hom

/-- The identity homomorphism.  Also the G5 inhabitant of `Rep.Hom`.

@census none (helper)
-/
protected def id (M : Rep Γ) : Hom M M where
  ψ _ := LinearMap.id
  edge _ _ := rfl
  rational _ _ _ := rfl

/-- Composition of homomorphisms of rational representations.

@census none (helper)
-/
protected def comp {M N P : Rep Γ} (f : Hom M N) (g : Hom N P) : Hom M P where
  ψ v := g.ψ v ∘ₗ f.ψ v
  edge e m := by
    simp only [LinearMap.coe_comp, Function.comp_apply, f.edge e m, g.edge e (f.ψ _ m)]
  rational σ v m := by
    simp only [LinearMap.coe_comp, Function.comp_apply, f.rational σ v m,
      g.rational σ v (f.ψ v m)]

/-- The identity homomorphism has identity components.  @census none (helper) -/
@[simp]
theorem id_ψ (M : Rep Γ) (v : Γ.V) : (Hom.id M).ψ v = LinearMap.id := rfl

/-- Composition is componentwise.  @census none (helper) -/
@[simp]
theorem comp_ψ {M N P : Rep Γ} (f : Hom M N) (g : Hom N P) (v : Γ.V) :
    (f.comp g).ψ v = g.ψ v ∘ₗ f.ψ v := rfl

end Hom

/-! ### G5 non-vacuity: a non-degenerate inhabitant -/

/-- The additive equivalence of `L` underlying `σ ∈ Gal(L/K)`; the semi-linear structure map of
the tautological representation `constL`.

@census none (helper)
-/
def galAddEquiv (σ : Gal(L/K)) : L ≃+ L := σ.toRingEquiv.toAddEquiv

/-- `galAddEquiv σ` acts as `σ`.  @census none (helper) -/
@[simp]
theorem galAddEquiv_apply (σ : Gal(L/K)) (a : L) : galAddEquiv σ a = σ a := rfl

/-- **G5 non-vacuity** (`WORKFLOW.md` §4/G5).  For *any* `K`-rational quiver `Γ_K` and any
`Gal(L/K)`-equivariant family of scalars `t : E → L`, the constant family `M(v) = L` with
`φ_{v,σ} = σ` and `φ_e = (t e) ·` is a `K`-rational representation of `Γ_K`.

This inhabitant is **non-degenerate** in every sense G5 asks for: the spaces `M(v) = L` are
nonzero, the semi-linear maps `φ_{v,σ} = σ` are the tautological Galois action (nontrivial
whenever `L ≠ K`), the vertex action is `Γ`'s own (nontrivial whenever `Γ_K` is non-split), and
for `t = 1` the edge maps are the identity, hence nonzero.  Taking `t = 0` instead gives a
*nilpotent* inhabitant (`Rep.constLZero`), which is what `Rep^nil(Γ_K)` needs.

@census none (helper: G5 inhabitant of `RQ2-1.08`)
-/
def constL (Γ : RationalQuiver K L) (t : Γ.E → L)
    (ht : ∀ (σ : Gal(L/K)) (e : Γ.E), t (σ • e) = σ (t e)) : Rep Γ where
  M _ := L
  φ σ _ := galAddEquiv σ
  semilinear σ _ a m := by
    simp only [galAddEquiv_apply, smul_eq_mul, map_mul]
  cocycle σ τ v m := by
    rw [mul_smul]
    simp only [galAddEquiv_apply, AlgEquiv.mul_apply]
  smooth x := by
    haveI := Γ.galois
    obtain ⟨v, m⟩ := x
    have hset : {σ : Gal(L/K) |
        (⟨σ • v, galAddEquiv σ m⟩ : (w : Γ.V) × L) = ⟨v, m⟩}
        = ((MulAction.stabilizer Gal(L/K) v : Set Gal(L/K))
            ∩ (MulAction.stabilizer Gal(L/K) m : Set Gal(L/K))) := by
      ext σ
      simp [Sigma.mk.injEq, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, eq_comm]
    rw [hset]
    exact (Γ.isOpen_stabilizer_V v).inter
      (stabilizer_isOpen_of_isIntegral (K := K) (L := L) m)
  φEdge e := LinearMap.mulLeft L (t e)
  edge_equivariance σ e m m' h := by
    haveI := Γ.galois
    have hm' : m' = σ m := by
      simpa [Sigma.mk.injEq, eq_comm] using congrArg (fun y : (w : Γ.V) × L => y.2) h
    rw [Γ.target_smul σ e]
    subst hm'
    simp only [LinearMap.mulLeft_apply, galAddEquiv_apply, map_mul, ht σ e]

/-- **G5 non-vacuity**: the constant representation with **identity** edge maps.  Its edge maps
are nonzero, so it is not the zero representation and not a representation with zero structure
maps.

@census none (helper: G5 inhabitant of `RQ2-1.08`)
-/
def constLOne (Γ : RationalQuiver K L) : Rep Γ :=
  constL Γ (fun _ => 1) (by intro σ e; simp)

/-- **G5 non-vacuity**: the constant representation with **zero** edge maps.  Its spaces and
semi-linear structure maps are still nonzero, but every path of positive length acts by zero, so
it inhabits `Rep^nil(Γ_K)` as well (`Quiver/Rep/Nilpotent.lean`).

@census none (helper: G5 inhabitant of `RQ2-1.08` and of `RQ2-1.10`'s nilpotent subcategory)
-/
def constLZero (Γ : RationalQuiver K L) : Rep Γ :=
  constL Γ (fun _ => 0) (by intro σ e; simp)

/-- **G5 non-degeneracy**: the fibres of `constL` are nonzero, so `Rep Γ` is not inhabited only
by the zero representation. -/
theorem constL_nontrivial (Γ : RationalQuiver K L) (t : Γ.E → L)
    (ht : ∀ (σ : Gal(L/K)) (e : Γ.E), t (σ • e) = σ (t e)) (v : Γ.V) :
    Nontrivial ((constL Γ t ht).M v) :=
  inferInstanceAs (Nontrivial L)

/-- **G5 non-degeneracy**: the edge maps of `constLOne` are the identity. -/
theorem constLOne_φEdge_apply (Γ : RationalQuiver K L) (e : Γ.E)
    (m : (constLOne Γ).M (Γ.toRQuiver.source e)) : (constLOne Γ).φEdge e m = m := by
  exact one_mul (M := L) m

/-- **G5 non-degeneracy**: the edge maps of `constLOne` are **not** zero, so the inhabitant does
not satisfy the all-trivial interpretation of `def:rationalrepresentations`(iii). -/
theorem constLOne_φEdge_ne_zero (Γ : RationalQuiver K L) (e : Γ.E) :
    (constLOne Γ).φEdge e ≠ 0 := by
  intro h
  have h1 : (1 : L) = 0 := by
    have h2 := LinearMap.congr_fun h (1 : L)
    exact (constLOne_φEdge_apply Γ e (1 : L)).symm.trans h2
  exact one_ne_zero h1

end Rep

end RationalQuiver

end RationalQuivers
