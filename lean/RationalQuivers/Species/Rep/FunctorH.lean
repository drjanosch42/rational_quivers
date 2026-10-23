import RationalQuivers.Species.Rep.FunctorF

/-!
# The functor `H : Rep(S(Γ_K)) → Rep(Γ_K)` (§2.6, census `RQ2-2.27`, `RQ2-2.28`)

Formalizes the two unlabelled propositions that construct `H` (`unlabeled:5`, `unlabeled:6`).

## The choice of `K`-rational structures is an argument, never hidden

Clause `RQ2-2.27-H2` fixes, for every `i`, a `K`-rational structure `W_{i,K} ⊆ W_i`
(`eq:KrationalWi`), and the census note is explicit that this is **a choice, and that `H` depends
on it up to natural isomorphism**. It is therefore an explicit argument `WK` of every declaration
below, never a `Classical.choice` inside a definition: hiding it would silently drop a hypothesis
the census marks load-bearing, and would make `H` look canonical when the source says it is not.
This is the same visibility principle as the mirror-twist hypothesis of `RQ2-2.19`.

## `M(v)` is indexed by the orbit, which removes every transport

`M(v) := W_{i,K} ⊗_K L` for `i = Gv` (`eq:MvforWi`) depends on `v` **only through its orbit**, and
`φ_{v,σ}(w ⊗ a) = w ⊗ σa` (`eq:varphi2`) does not move `w` at all — it twists the scalar. So
`M(σ v)` and `M(v)` are the *same* space and `φ_{v,σ}` is an automorphism of it. Indexing `hObj`
by `Γ.VertexOrbit` rather than by `Γ.V` makes that a definitional fact instead of a transport, and
the cocycle condition `eq:semi-linearactiononrep` then has no `cast` in it at all. `M(v)` itself is
`hObj V WK (Γ.vertexClass v)`, and `vertexClass_smul` is the one lemma relating the two indexings —
used only in the continuity clause, which genuinely speaks about vertices.

This is stage S2's design decision for `Rep` (state the semi-linear conditions where no transport
occurs) reaching the same conclusion from the other side.
-/

universe u

namespace RationalQuivers

open MulAction CategoryTheory

open scoped TensorProduct DirectSum

namespace RationalQuiver

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  {Γ : RationalQuiver K L}

/-- The orbit of a vertex is `Gal(L/K)`-invariant.  @census none (helper) -/
theorem vertexClass_smul (σ : Gal(L/K)) (v : Γ.V) :
    Γ.vertexClass (σ • v) = Γ.vertexClass v := Quotient.sound ⟨σ, rfl⟩

/-- **`M(v) := W_{i,K} ⊗_K L`** for `i = Gv` (`eq:MvforWi`), indexed by the orbit — see the module
header for why that is the right indexing.  Written in mathlib's base-change factor order.

@census none (clause witness for `RQ2-2.27-H3`)
@clauses   RQ2-2.27-H3
-/
noncomputable abbrev hObj (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i)) (i : Γ.VertexOrbit) : Type u :=
  L ⊗[K] ↥(WK i)

/-- Transport of `hObj` along an equality of vertex orbits.

**Named, not `▸`.**  The transport doctrine (`CONVENTIONS.md`; S4's rule, restated for `RQ2-2.23`'s
`Θ`) is that a dependent transport is paid **once, in a named definition inside the infrastructure**
and never written inline in a summit statement.  `RQ2-2.27-C3` needs to compare `φ σ` applied over
`vertexClass v` with an element indexed by `vertexClass (σ • v)`; those orbits are equal
(`vertexClass_smul`) but not syntactically so, and the statement used to carry a bare `▸`.  It now
consumes this definition instead.

@census none (helper) -/
noncomputable def hObjCast (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i)) {i i' : Γ.VertexOrbit} (h : i = i') :
    hObj V WK i ≃+ hObj V WK i' := h ▸ AddEquiv.refl _

@[simp] theorem hObjCast_rfl (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i)) (i : Γ.VertexOrbit)
    (x : hObj V WK i) : hObjCast V WK (rfl : i = i) x = x := rfl

/-! ### `RQ2-2.27-H2` — what it means to FIX a `K`-rational structure

Finding **V-S5b-2**.  The clause reads "for every `i` a **`K`-rational structure** `W_{i,K}` inside
`W_i` is fixed (`eq:KrationalWi`)".  A bare `WK : ∀ i, Submodule K (V.W i)` carries none of that:
it is an arbitrary `K`-subspace, and `WK i := ⊥` then refutes the row.  The source *derives*
`C4` from `H2` — "Observe first that we have an isomorphism `W_{i,K} ⊗_K L_i → W_i`" — so `H2` is
the hypothesis and `C4` its immediate consequence, not the other way round.

`IsKRationalStructure` states `H2` the way descent theory does, and deliberately **not** as
`Nonempty (L_i ⊗[K] W_{i,K} ≃ₗ W_i)`: it requires the **canonical** map `a ⊗ w ↦ a · w` to be
bijective.  That is strictly stronger than the existence of *some* isomorphism (which two spaces of
equal dimension always have, carrying no information about `W_{i,K}` sitting inside `W_i`), and it
is what `eq:KrationalWi` actually says.  `C4` is then its restatement, kept as a conclusion exactly
as the source keeps it as an observation.

@census none (helper: clause `RQ2-2.27-H2`, `RQ2-2.28-H2`, `RQ2-2.29`)
@clauses   RQ2-2.27-H2
-/
def IsKRationalStructure (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit)
    (WKi : Submodule K (V.W i)) : Prop :=
  Function.Bijective
    (LinearMap.liftBaseChange (Γ.toSpecies.L i) ((WKi.subtype).restrictScalars K))

/-- `eq:KrationalWi` on pure tensors: the canonical map is `a ⊗ w ↦ a · w`.
@census none (helper) -/
theorem isKRationalStructure_apply (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit)
    (WKi : Submodule K (V.W i)) (a : Γ.toSpecies.L i) (w : ↥WKi) :
    LinearMap.liftBaseChange (Γ.toSpecies.L i) ((WKi.subtype).restrictScalars K) (a ⊗ₜ w)
      = a • (w : V.W i) := rfl

/-- **Clause `RQ2-2.27-C4`** follows from `H2`, as in the source.  @census none (helper)
@clauses   RQ2-2.27-C4 -/
theorem nonempty_baseChange_of_isKRationalStructure
    {V : EtaleSpecies.Rep Γ.toSpecies} {i : Γ.VertexOrbit} {WKi : Submodule K (V.W i)}
    (h : IsKRationalStructure V i WKi) :
    Nonempty ((Γ.toSpecies.L i) ⊗[K] ↥WKi ≃ₗ[(Γ.toSpecies.L i)] V.W i) :=
  ⟨LinearEquiv.ofBijective _ h⟩

/-! ### `RQ2-2.27`'s `φ_{v,σ}` — clauses `C1`, `C2`, `C3`  (G4)

`φ_{v,σ}` is `σ ⊗ 1` on `M(v) = L ⊗_K W_{i,K}` (`hPhi`), so `C1`'s pin is `rfl`, its
`σ`-linearity and `C2`'s cocycle law are one tensor induction each, and `φ_{v,1} = id` comes free.

**`C3` is the continuity clause, and it is stated over a `Σ`-type**, so the whole difficulty is the
dependent transport.  Three steps keep it out of the argument:

* `hObjCast_heq` — the transport is heterogeneously the identity, which is all one ever needs of it;
* `hSigma_eq_iff` — membership in `C3`'s set is **cast-free**: `σ • v = v` and `φ_σ y = y`.  With
  that the set is visibly a subgroup (`hPhiStab`), which is what makes `Subgroup.isOpen_of_mem_nhds`
  applicable — the §42 shape;
* `hPhi_exists_fixing_field` — every `y` is fixed by the elements fixing *some* finite intermediate
  field, proved by tensor induction (`⊥` / `K⟮a⟯` / `E₁ ⊔ E₂`).  `E.fixingSubgroup` is then open by
  mathlib's `IntermediateField.fixingSubgroup_isOpen`, and its intersection with the open
  `G_v` (clause `RQ2-1.02-C2`) is the open neighbourhood of `1` inside the stabiliser.

So `C3` is `RQ2-1.02-C2` and the Krull topology's own basis, and nothing else — which is exactly
what the row claims: the action is continuous *because* it is obtained by base change from a
continuous `G`-set.

@census none (G4 engine for `RQ2-2.27`)
-/

/-- **`φ_{v,σ}` of `eq:varphi2`**: `σ ⊗ 1` on `M(v) = W_{i,K} ⊗_K L`. -/
noncomputable def hPhi (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i)) (σ : Gal(L/K)) (i : Γ.VertexOrbit) :
    hObj V WK i ≃+ hObj V WK i :=
  (TensorProduct.congr (σ.toLinearEquiv) (LinearEquiv.refl K ↥(WK i))).toAddEquiv

@[simp] theorem hPhi_tmul (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i)) (σ : Gal(L/K)) (i : Γ.VertexOrbit)
    (a : L) (w : ↥(WK i)) : hPhi V WK σ i (a ⊗ₜ w) = σ a ⊗ₜ w := rfl

/-- **Clause `RQ2-2.27-C1`**, second half: `φ_{v,σ}` is `σ`-linear. -/
theorem hPhi_smul (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i)) (σ : Gal(L/K)) (i : Γ.VertexOrbit)
    (a : L) (x : hObj V WK i) : hPhi V WK σ i (a • x) = σ a • hPhi V WK σ i x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b w =>
      show hPhi V WK σ i ((a * b) ⊗ₜ w) = σ a • ((σ b) ⊗ₜ[K] w)
      rw [hPhi_tmul, map_mul]
      rfl
  | add p q hp hq => rw [smul_add, map_add, map_add, hp, hq, smul_add]

/-- **Clause `RQ2-2.27-C2`**: the cocycle condition. -/
theorem hPhi_comp (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i)) (σ τ : Gal(L/K)) (i : Γ.VertexOrbit)
    (x : hObj V WK i) : hPhi V WK σ i (hPhi V WK τ i x) = hPhi V WK (σ * τ) i x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b w => rw [hPhi_tmul, hPhi_tmul, hPhi_tmul, AlgEquiv.mul_apply]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]

/-- `φ_{v,1} = id`. -/
theorem hPhi_one (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i)) (i : Γ.VertexOrbit)
    (x : hObj V WK i) : hPhi V WK 1 i x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b w => rw [hPhi_tmul]; rfl
  | add p q hp hq => rw [map_add, hp, hq]

/-- `hObjCast` is a transport: it is heterogeneously the identity. -/
theorem hObjCast_heq (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i)) {i i' : Γ.VertexOrbit} (h : i = i')
    (x : hObj V WK i) : HEq (hObjCast V WK h x) x := by
  subst h; rfl

/-- Membership in `RQ2-2.27-C3`'s set, cast-free. -/
theorem hSigma_eq_of (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i)) (σ : Gal(L/K)) (v : Γ.V)
    (y : hObj V WK (Γ.vertexClass v)) (hv : σ • v = v)
    (hy : hPhi V WK σ (Γ.vertexClass v) y = y) :
    (⟨σ • v, hObjCast V WK (vertexClass_smul σ v).symm
        (hPhi V WK σ (Γ.vertexClass v) y)⟩ : Σ v : Γ.V, hObj V WK (Γ.vertexClass v))
      = ⟨v, y⟩ := by
  refine Sigma.ext hv ?_
  rw [hy]
  exact hObjCast_heq V WK _ y

theorem hSigma_eq_iff (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i)) (σ : Gal(L/K)) (v : Γ.V)
    (y : hObj V WK (Γ.vertexClass v)) :
    ((⟨σ • v, hObjCast V WK (vertexClass_smul σ v).symm
        (hPhi V WK σ (Γ.vertexClass v) y)⟩ : Σ v : Γ.V, hObj V WK (Γ.vertexClass v))
      = ⟨v, y⟩)
      ↔ (σ • v = v ∧ hPhi V WK σ (Γ.vertexClass v) y = y) := by
  constructor
  · intro h
    rw [Sigma.mk.injEq] at h
    refine ⟨h.1, eq_of_heq ?_⟩
    exact ((hObjCast_heq V WK (vertexClass_smul σ v).symm
      (hPhi V WK σ (Γ.vertexClass v) y)).symm.trans h.2)
  · exact fun h => hSigma_eq_of V WK σ v y h.1 h.2

/-- The stabiliser of a point of `⊔_v M(v)`, as a subgroup. -/
def hPhiStab (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i)) (v : Γ.V)
    (y : hObj V WK (Γ.vertexClass v)) : Subgroup Gal(L/K) where
  carrier := {σ | σ • v = v ∧ hPhi V WK σ (Γ.vertexClass v) y = y}
  one_mem' := ⟨one_smul _ v, hPhi_one V WK (Γ.vertexClass v) y⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨by rw [mul_smul, hb.1, ha.1], by rw [← hPhi_comp, hb.2, ha.2]⟩
  inv_mem' := fun {a} ha =>
    ⟨by rw [inv_smul_eq_iff, ha.1], by
      have := hPhi_comp V WK a⁻¹ a (Γ.vertexClass v) y
      rw [ha.2, inv_mul_cancel] at this
      rw [this, hPhi_one]⟩

/-- Every element of `M(v) = L ⊗_K W_{i,K}` is fixed by the elements of `Gal(L/K)` fixing some
finite intermediate field. -/
theorem hPhi_exists_fixing_field (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i)) (i : Γ.VertexOrbit) (y : hObj V WK i) :
    ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      ∀ σ ∈ E.fixingSubgroup, hPhi V WK σ i y = y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨⊥, inferInstance, fun σ _ => map_zero _⟩
  | tmul a w =>
      haveI : FiniteDimensional K (IntermediateField.adjoin K {a}) :=
        IntermediateField.adjoin.finiteDimensional
          (Algebra.IsIntegral.isIntegral (R := K) a)
      refine ⟨IntermediateField.adjoin K {a}, inferInstance, fun σ hσ => ?_⟩
      rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
      rw [hPhi_tmul]
      congr 1
      exact hσ a (IntermediateField.subset_adjoin K {a} rfl)
  | add p q hp hq =>
      obtain ⟨E₁, h₁, hf₁⟩ := hp
      obtain ⟨E₂, h₂, hf₂⟩ := hq
      haveI := h₁; haveI := h₂
      refine ⟨E₁ ⊔ E₂, IntermediateField.finiteDimensional_sup E₁ E₂, fun σ hσ => ?_⟩
      rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
      have hm₁ : σ ∈ E₁.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        exact fun z hz => hσ z ((le_sup_left : E₁ ≤ E₁ ⊔ E₂) hz)
      have hm₂ : σ ∈ E₂.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        exact fun z hz => hσ z ((le_sup_right : E₂ ≤ E₁ ⊔ E₂) hz)
      rw [map_add, hf₁ σ hm₁, hf₂ σ hm₂]

/-- **Clause `RQ2-2.27-C3`**: the `G`-action on `⊔_v M(v)` is continuous, in open-stabiliser form. -/
theorem hPhi_isOpen (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i))
    (x : Σ v : Γ.V, hObj V WK (Γ.vertexClass v)) :
    IsOpen {σ : Gal(L/K) | (⟨σ • x.1,
      hObjCast V WK (vertexClass_smul σ x.1).symm (hPhi V WK σ (Γ.vertexClass x.1) x.2)⟩ :
      Σ v : Γ.V, hObj V WK (Γ.vertexClass v)) = x} := by
  obtain ⟨v, y⟩ := x
  have hset : {σ : Gal(L/K) | (⟨σ • v,
      hObjCast V WK (vertexClass_smul σ v).symm (hPhi V WK σ (Γ.vertexClass v) y)⟩ :
      Σ v : Γ.V, hObj V WK (Γ.vertexClass v)) = ⟨v, y⟩}
      = ((hPhiStab V WK v y : Subgroup Gal(L/K)) : Set Gal(L/K)) := by
    ext σ
    exact hSigma_eq_iff V WK σ v y
  rw [hset]
  obtain ⟨E, hE, hfix⟩ := hPhi_exists_fixing_field V WK (Γ.vertexClass v) y
  haveI := hE
  have hopen : IsOpen ((MulAction.stabilizer Gal(L/K) v : Set Gal(L/K))
      ∩ (E.fixingSubgroup : Set Gal(L/K))) :=
    (Γ.isOpen_stabilizer_V v).inter (IntermediateField.fixingSubgroup_isOpen E)
  have hsub : ((MulAction.stabilizer Gal(L/K) v : Set Gal(L/K))
      ∩ (E.fixingSubgroup : Set Gal(L/K)))
      ⊆ ((hPhiStab V WK v y : Subgroup Gal(L/K)) : Set Gal(L/K)) := by
    rintro σ ⟨h1, h2⟩
    exact ⟨h1, hfix σ h2⟩
  exact Subgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset (hopen.mem_nhds ⟨one_mem _, one_mem _⟩) hsub)

/-! ### `RQ2-2.27-C5` — the `(ε,η)`-summand, identified  (G4)

The row's own G4 plan: *use `RQ2-2.19`, then `C4` to replace `W_i` by `W_{i,K} ⊗_K L_i`, with the
finite product identified with the finite direct sum.*  This is the middle step, and it is what
makes `eq:WiiMjL2`'s right-hand side come out as `M(v)` **on the nose** rather than up to a further
identification:

```
Twist(L(e_ε),ρ) ⊗_{TwistBase} (L(e_ε) ⊗_{L_i} W_i)
    --C4-->        Twist(L(e_ε),ρ) ⊗_{TwistBase} (L(e_ε) ⊗_K W_{i,K})
    --twistAbsorb--> L ⊗_K W_{i,K}  =  hObj V WK i  =  M(v).
```

Two small pieces make the middle arrow go through, and both are `§51`-shaped:

* `linearEquivTwistBaseOfE` — an `↥E`-linear equivalence **is** `TwistBase E ρ`-linear, both module
  structures being `compHom`s along `toE`.  Stated rather than assumed, because the two are
  different types;
* `twistLTensorCongr` — transporting the second factor of `Twist ⊗_{TwistBase} −` is `L`-linear,
  since `L` acts through the `Twist` factor.  `AlgebraTensorModule.congr` is **not** usable here:
  it wants `Algebra (TwistBase E ρ) L`, and adding that instance would compete with
  `Twist.instModuleBaseL` at one head.  So the upgrade is the stage's usual `AddEquiv`-plus-pin.

@census none (G4 engine for `RQ2-2.27-C5`)
-/

section C5
variable (V : EtaleSpecies.Rep Γ.toSpecies)
  (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i))

/-- **Clause `RQ2-2.27-C4` as an equivalence**: `W_{i,K} ⊗_K L_i ≅ W_i`. -/
noncomputable def kRatEquiv {i : Γ.VertexOrbit} (h : IsKRationalStructure V i (WK i)) :
    ((Γ.toSpecies.L i) ⊗[K] ↥(WK i)) ≃ₗ[Γ.toSpecies.L i] V.W i :=
  LinearEquiv.ofBijective _ h

/-- **The transport `C5` needs**: `L(e_ε) ⊗_{L_i} W_i ≅ L(e_ε) ⊗_K W_{i,K}`, `L(e_ε)`-linearly,
so that it transports across `Twist ⊗_{TwistBase} −`. -/
noncomputable def edgeSummandKRat {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (h : IsKRationalStructure V i (WK i)) :
    edgeSummandG (V.W i) ε ≃ₗ[↥(Γ.edgeOrbitField ε)]
      (↥(Γ.edgeOrbitField ε) ⊗[K] ↥(WK i)) := by
  letI := edgeLeftAlgebraSpecies ε
  haveI : IsScalarTower K (Γ.toSpecies.L i) ↥(Γ.edgeOrbitField ε) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      ((Γ.edgeComponentLeft ε).commutes c).symm
  exact (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl ↥(Γ.edgeOrbitField ε) ↥(Γ.edgeOrbitField ε))
      (kRatEquiv V WK h).symm).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      K (Γ.toSpecies.L i) ↥(Γ.edgeOrbitField ε) ↥(Γ.edgeOrbitField ε) ↥(WK i))

/-- An `↥E`-linear equivalence is `TwistBase E ρ`-linear, both module structures being
`compHom`s along `toE`. -/
noncomputable def linearEquivTwistBaseOfE {E : IntermediateField K L} {ρ : Gal(L/K)}
    {A B : Type u} [AddCommGroup A] [AddCommGroup B] [Module ↥E A] [Module ↥E B]
    [Module (Twist.TwistBase E ρ) A] [Module (Twist.TwistBase E ρ) B]
    (hA : ∀ (b : Twist.TwistBase E ρ) (a : A), b • a = (b.val : ↥E) • a)
    (hB : ∀ (b : Twist.TwistBase E ρ) (a : B), b • a = (b.val : ↥E) • a)
    (f : A ≃ₗ[↥E] B) : A ≃ₗ[Twist.TwistBase E ρ] B where
  toFun := f
  invFun := f.symm
  map_add' := f.map_add
  map_smul' b a := by
    show f (b • a) = b • f a
    rw [hA, map_smul, ← hB]
  left_inv := f.left_inv
  right_inv := f.right_inv

/-- Transporting the second factor of `Twist ⊗_{TwistBase} −` along a `TwistBase`-linear
equivalence is `L`-linear, because `L` acts through the `Twist` factor.

`AlgebraTensorModule.congr` is not available here: it would want `Algebra (TwistBase E ρ) L`, and
adding that instance would compete with `Twist.instModuleBaseL` at one head — §51's rule again.
So the upgrade is the stage's usual one, `AddEquiv` plus the pin. -/
noncomputable def twistLTensorCongr {E : IntermediateField K L} {ρ : Gal(L/K)}
    {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [Module (Twist.TwistBase E ρ) A] [Module (Twist.TwistBase E ρ) B]
    (g : A ≃ₗ[Twist.TwistBase E ρ] B) :
    (Twist E ρ ⊗[Twist.TwistBase E ρ] A) ≃ₗ[L] (Twist E ρ ⊗[Twist.TwistBase E ρ] B) :=
  AddEquiv.toLinearEquiv
    (TensorProduct.congr (LinearEquiv.refl (Twist.TwistBase E ρ) (Twist E ρ)) g).toAddEquiv
    (fun c z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul t a =>
          show (TensorProduct.congr (LinearEquiv.refl (Twist.TwistBase E ρ) (Twist E ρ)) g)
              ((c • t) ⊗ₜ[Twist.TwistBase E ρ] a)
            = c • (TensorProduct.congr
                (LinearEquiv.refl (Twist.TwistBase E ρ) (Twist E ρ)) g)
                (t ⊗ₜ[Twist.TwistBase E ρ] a)
          rw [TensorProduct.congr_tmul, TensorProduct.congr_tmul]
          rfl
      | add p q hp hq => rw [smul_add, map_add, map_add, hp, hq, smul_add])

/-- **The `(ε,η)`-summand of `eq:WiiMjL2`, identified**: through clause `C4` and the twist
absorbing its own base, it is `M(v) = L ⊗_K W_{i,K}` **on the nose**. -/
noncomputable def wiiMjL2Summand {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) (ρ : Gal(L/K))
    (h : IsKRationalStructure V i (WK i)) :
    (Twist (Γ.edgeOrbitField ε) ρ
      ⊗[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandG (V.W i) ε)
      ≃ₗ[L] hObj V WK i :=
  (twistLTensorCongr
      (linearEquivTwistBaseOfE
        (twistBase_smul_edgeSummandG (V.W i) ε ρ)
        (twistBase_smul_tensorK (Γ.edgeOrbitField ε) ρ ↥(WK i))
        (edgeSummandKRat V WK ε h))).trans
    (twistAbsorb (Γ.edgeOrbitField ε) ρ ↥(WK i))

end C5

/-! ### `RQ2-2.27-C5`/`C6` — `eq:WiiMjL2`, assembled  (G4)

The chain is `RQ2-2.20`'s, at the carrier `V.W i` instead of `M(v_i)^{G_{v_i}}` and with the
`(ε,η)`-summand landing on `M(v)` by `wiiMjL2Summand`:

```
Balanced K L_j L L (W_i ⊗_{L_i} {}_iM_j)
  --outerEquivL-->   L ⊗_{L(v_j)} (W_i ⊗_{L_i} {}_iM_j)
  --innerEquivH-->   L ⊗_{L(v_j)} ({}_iM_j ⊗_{L_i} W_i)
  --piSplitVOFH-->   L ⊗_{L(v_j)} (∀ ε, L(e_ε) ⊗_{L_i,σ_ε} W_i)
  --piRight-->       ∀ ε, L ⊗_{L(v_j)} (L(e_ε) ⊗_{L_i,σ_ε} W_i)
  --RQ2-2.19-->       ∀ ε, ∀ η, Twist(L(e_ε), ητ_ε⁻¹) ⊗ (L(e_ε) ⊗_{L_i,σ_ε} W_i)
  --wiiMjL2Summand-> ∀ ε, ∀ η, M(v)
  --DirectSum ×2-->  ⊕_ε ⊕_η M(v)
```

Only the first four links needed anything new, and only because `RQ2-2.20`'s were written at the
one carrier: `outerEquivL` was already generic, and `innerEquivH`/`piSplitH`/`piSplitVOFH` are its
siblings at `V.W i`, one line of content each (`Balanced.equivTensor`, `TensorProduct.piLeft`, and
the `L_j`-linear upgrade `eq:edgediagram`'s right half supplies).

**`C6` is `finite_cosetIndex` doing the same job a fourth time** (§41's table): `η` runs over a
*finite* index set, which is what lets the product become a **direct sum** —
`DirectSum.linearEquivFunOnFintype`, applied twice.  Without clause `RQ2-1.02-C3` this clause's
statement would not even typecheck as written.

@census none (G4 engine for `RQ2-2.27-C5`, `RQ2-2.27-C6`)
-/

section C5Chain
variable (V : EtaleSpecies.Rep Γ.toSpecies) (i j : Γ.VertexOrbit)

/-- `{}_iM_j ⊗_{L_i} W_i` over `L_j`, from its right action.  @census none (helper, `S5-F3`) -/
noncomputable instance moduleSpeciesLj_innerTensorH :
    Module (Γ.toSpecies.L j) (Γ.toSpecies.M i j ⊗[Γ.toSpecies.L i] (V.W i)) :=
  moduleOfOpposite _ _

/-- …re-headed.  @census none (helper, `S5-F3`) -/
noncomputable instance moduleVOFj_innerTensorH :
    Module ↥(Γ.vertexOrbitField j) (Γ.toSpecies.M i j ⊗[Γ.toSpecies.L i] (V.W i)) :=
  inferInstanceAs (Module (Γ.toSpecies.L j) _)

/-- `innerEquiv` at `V.W i`, upgraded to `L_j`-linear at the frozen head. -/
noncomputable def innerEquivH :
    EtaleSpecies.Rep.tensor Γ.toSpecies i j (V.W i)
      ≃ₗ[↥(Γ.vertexOrbitField j)]
      (Γ.toSpecies.M i j ⊗[Γ.toSpecies.L i] (V.W i)) :=
  AddEquiv.toLinearEquiv
    (Balanced.equivTensor (K := K) (A := Γ.toSpecies.L i) (B := Γ.toSpecies.L j)
      (X := V.W i) (fun _ _ => rfl)).toAddEquiv
    (fun c x => by
      exact (Balanced.equivTensor (K := K) (A := Γ.toSpecies.L i) (B := Γ.toSpecies.L j)
        (X := V.W i) (fun _ _ => rfl)).map_smul (MulOpposite.op c) x)

/-- The splitting at `V.W i`, over `L_i`. -/
noncomputable def piSplitH :
    (Γ.toSpecies.M i j ⊗[Γ.toSpecies.L i] (V.W i))
      ≃ₗ[Γ.toSpecies.L i] (∀ ε : Γ.EdgeOrbit i j, edgeSummandG (V.W i) ε) := by
  classical
  letI : Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
  letI : ∀ ε : Γ.EdgeOrbit i j, Module (Γ.toSpecies.L i) ↥(Γ.edgeOrbitField ε) :=
    fun ε => (edgeLeftAlgebraSpecies ε).toModule
  exact TensorProduct.piLeft _ _ _

@[simp] theorem piSplitH_tmul (m : Γ.toSpecies.M i j) (w : V.W i) (ε : Γ.EdgeOrbit i j) :
    piSplitH V i j (m ⊗ₜ[Γ.toSpecies.L i] w) ε
      = (letI := edgeLeftAlgebraSpecies ε; (m ε) ⊗ₜ[Γ.toSpecies.L i] w) := by
  classical
  letI : Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
  letI : ∀ ε : Γ.EdgeOrbit i j, Module (Γ.toSpecies.L i) ↥(Γ.edgeOrbitField ε) :=
    fun ε => (edgeLeftAlgebraSpecies ε).toModule
  show TensorProduct.piLeft _ _ _ (m ⊗ₜ[Γ.toSpecies.L i] w) ε = _
  simp [TensorProduct.piLeft, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]

/-- …upgraded to `L_j`-linear: `L_j` acts on the source through `{}_iM_j`'s right action and on
the target componentwise through `edgeComponentRight`. -/
noncomputable def piSplitVOFH :
    (Γ.toSpecies.M i j ⊗[Γ.toSpecies.L i] (V.W i))
      ≃ₗ[↥(Γ.vertexOrbitField j)] (∀ ε : Γ.EdgeOrbit i j, edgeSummandG (V.W i) ε) :=
  AddEquiv.toLinearEquiv (piSplitH V i j).toAddEquiv (fun c z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m w =>
        funext ε
        show piSplitH V i j ((MulOpposite.op c • m) ⊗ₜ[Γ.toSpecies.L i] w) ε
          = c • (piSplitH V i j (m ⊗ₜ[Γ.toSpecies.L i] w) ε)
        rw [piSplitH_tmul, piSplitH_tmul]
        rfl
    | add p q hp hq => rw [smul_add, map_add, map_add, hp, hq, smul_add])

open scoped Classical in
/-- **`eq:WiiMjL2` as a named equivalence.**  `RQ2-2.27-C5` states it as `Nonempty`, but `RQ2-2.28`'s
`φ_e` is *the displayed composite through it*, so the map itself has to be nameable.  The `RQ2-2.19`
identification per edge orbit is taken by `Exists.choose`; nothing downstream depends on which,
because `IsEdgeDescent`'s pin — not this choice — is what fixes the descent (`edgeDescent_unique`).
**That sentence was false before finding `S5-F8`'s repair** (§56): with `e₀` unconstrained the
descent was not unique, and `φ_e` below would have inherited an unpinned choice.

**And it is true only of the descent** (§62.5).  `Exists.choose` here is harmless for the *descent*,
which `IsEdgeDescent`'s pin fixes; it is **fatal** for any property of the *map* — and `RQ2-2.28`'s
edge datum needs exactly such a property (`hfix`).  What rescues it is that this `Exists` is not
bare: `leEpsilon_at_edgeSummandG` carries `RQ2-2.20-C1`'s pin `e (a ⊗ₜ v) η = Twist.ofL a ⊗ₜ v`, so
`.choose_spec` determines the chosen map on generators and the chain computes.  Both halves of the
sentence are load-bearing, in opposite directions.

@census none (helper for `RQ2-2.27-C5` and `RQ2-2.28`) -/
noncomputable def wiiMjL2Equiv (WK : ∀ k : Γ.VertexOrbit, Submodule K (V.W k))
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch i j ε))] :
    Balanced K (Γ.toSpecies.L j) L L
        (EtaleSpecies.Rep.tensor Γ.toSpecies i j (V.W i))
      ≃ₗ[L] ⨁ ε : Γ.EdgeOrbit i j,
        ⨁ _η : EdgeChoice.CosetIndex Γ (ch i j ε), hObj V WK i :=
  (outerEquivL i j (V.W i)).trans <|
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
        ((innerEquivH V i j).trans (piSplitVOFH V i j))).trans <|
      (TensorProduct.piRight _ _ _ _).trans <|
        (LinearEquiv.piCongrRight (fun ε : Γ.EdgeOrbit i j =>
          (leEpsilon_at_edgeSummandG (V.W i) (ch i j ε)).choose)).trans <|
          (LinearEquiv.piCongrRight (fun ε =>
            (LinearEquiv.piCongrRight (fun η =>
              wiiMjL2Summand V WK ε
                (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹) (hWK i))).trans
              (DirectSum.linearEquivFunOnFintype L _ _).symm)).trans
            (DirectSum.linearEquivFunOnFintype L _ _).symm

open scoped Classical in
/-- **Clauses `RQ2-2.27-C5`/`C6`** (`eq:WiiMjL2`): `W_i ⊗_{L_i} {}_iM_j ⊗_{L_j} L = ⊕_ε ⊕_η M(v)`,
with a **direct sum** over `η`. -/
theorem wiiMjL2_nonempty (WK : ∀ k : Γ.VertexOrbit, Submodule K (V.W k))
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε) :
    Nonempty (Balanced K (Γ.toSpecies.L j) L L
        (EtaleSpecies.Rep.tensor Γ.toSpecies i j (V.W i))
      ≃ₗ[L] ⨁ ε : Γ.EdgeOrbit i j,
        ⨁ _η : EdgeChoice.CosetIndex Γ (ch i j ε), hObj V WK i) := by
  classical
  letI : Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
  letI : ∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch i j ε)) :=
    fun ε => @Fintype.ofFinite _ (finite_cosetIndex (ch i j ε))
  exact ⟨wiiMjL2Equiv V i j WK hWK ch⟩

end C5Chain

/-- **Proposition** (`unlabeled:5`, census `RQ2-2.27`).

Given a representation `(W_i, f_{ij})` of `S(Γ_K)` (clause `RQ2-2.27-H1`), a **chosen** `K`-rational
structure `W_{i,K} ⊆ W_i` for each `i` (clause `RQ2-2.27-H2`, the argument `WK`), and
`M(v) := W_{i,K} ⊗_K L` for `i = Gv` (clause `RQ2-2.27-H3`, `hObj`):

* `φ_{v,σ} : M(v) → M(σ v)`, `w ⊗ a ↦ w ⊗ σ a`, is a canonical `σ`-linear **isomorphism**
  (`eq:varphi2`, clause `RQ2-2.27-C1`);
* these satisfy the **cocycle** condition `eq:semi-linearactiononrep` (clause `RQ2-2.27-C2`);
* the resulting `G`-action on `⊔_v M(v)` is **continuous**, being obtained by base change from the
  `K`-rational structures with `V` a continuous `G`-set (clause `RQ2-2.27-C3`);
* `W_{i,K} ⊗_K L_i → W_i` is an **isomorphism** (clause `RQ2-2.27-C4`);
* and there is a canonical isomorphism `eq:WiiMjL2`,
  `W_i ⊗_{L_i} {}_iM_j ⊗_{L_j} L = ⊕_ε ⊕_η M(η τ_ε^{-1} σ_ε v_i)` (clause `RQ2-2.27-C5`), with `η`
  running through a system of representatives for `G_{v_j}/G_{τ_ε^{-1}e_ε}` (clause `RQ2-2.27-C6`).

@census    RQ2-2.27
@source    prop:hdecomposition
@clauses   RQ2-2.27-H1, RQ2-2.27-H2, RQ2-2.27-H3, RQ2-2.27-C1, RQ2-2.27-C2, RQ2-2.27-C3, RQ2-2.27-C4,
           RQ2-2.27-C5, RQ2-2.27-C6
@imports   none
@divergence JUSTIFIED_REFORMULATION on clauses `RQ2-2.27-C1` and `RQ2-2.27-C2`; WEAKENED_OR_PARTIAL on
the word "canonical" in clauses `RQ2-2.27-C4` and `RQ2-2.27-C5` (**added 2026-10-03**, docstring-only
`R-PROC-4` amendment of frozen S5, coordinator ruling `R-FR-9`, final-release WP-16b,
`MISMATCH-TRIAGE.md` row #15). The last two conjuncts assert only `Nonempty (… ≃ₗ …)`. The canonical
maps exist in the tree as named definitions and are what every downstream use goes through:
`kRatEquiv` (`LinearEquiv.ofBijective` of the canonical `L_i ⊗_K W_{i,K} → W_i`, bijective by `hWK`)
for `C4`, and `wiiMjL2Equiv` (the source's chain for `eq:WiiMjL2`; used by `hFunctor` and
`hFunctor_hH3`) for `C5`. This statement does not pin either isomorphism to them. The divergence
pre-dates census r18, which changed only the proof text, and was undisclosed until this amendment.

Both `C1` and `C2` are stated with `M(−)` indexed by the **orbit** rather than by the vertex, so that `M(σ v)`
and `M(v)` are the same type and `φ_{v,σ}` is an automorphism.  That is not a weakening: `M(v)`
depends on `v` only through `Gv` by clause `H3` itself, and `eq:varphi2` moves only the scalar.  It
removes every `cast` from `C1` and `C2` — the transport hazard stage S2 identified as the
archetypal `WEAKENED_OR_PARTIAL` shape for exactly these two conditions.  The vertex-indexed
reading is recovered as `hObj V WK (Γ.vertexClass v)`, and `C3`, which genuinely quantifies over
vertices, is stated that way, on the disjoint union, in the open-stabilizer form
`census/NOTATION.md` §12 prescribes and stage S2 used for `RQ2-1.08-C6`.

**Clause `C5`'s inner index is a `⊕`, not a `∏`** — the census note flags the contrast with
`eq:WiiMjL` explicitly, and the two are written differently here for that reason: `RQ2-2.20`/
`RQ2-2.22` have `⨁ ε, (∀ η, —)`, this row has `⨁ ε, ⨁ η, —`. The difference is real when
`G_{v_j}/G_{τ_ε^{-1}e_ε}` is infinite, and it is what makes `H`'s decomposition a *sum* the edge
maps can be defined summand-by-summand on.

Proof plan (G4): `C1`/`C2` are `TensorProduct` base change along `σ`, with the cocycle immediate
from `σ(τ a) = (στ) a`; `C3` is `Rep.constL`'s argument — the stabilizer of `w ⊗ a` contains the
intersection of the stabilizer of `v` with that of `a`, both open; `C4` is the definition of a
`K`-rational structure (`RQ2-1.16`) plus Galois descent; `C5` is the source's own chain, using
`RQ2-2.19` and then `C4` to replace `W_i` by `W_{i,K} ⊗_K L_i`, with the finite product identified
with the finite direct sum.
-/
theorem H_decomposition (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i))
    (hWK : ∀ i : Γ.VertexOrbit, IsKRationalStructure V i (WK i))
    (ch : ∀ (i j : Γ.VertexOrbit) (ε : Γ.EdgeOrbit i j), Γ.EdgeChoice ε) :
    ∃ φ : ∀ (_ : Gal(L/K)) (i : Γ.VertexOrbit), hObj V WK i ≃+ hObj V WK i,
      -- `C1`: `eq:varphi2`, and `σ`-linearity
      (∀ (σ : Gal(L/K)) (i : Γ.VertexOrbit) (a : L) (w : ↥(WK i)),
        φ σ i (a ⊗ₜ w) = σ a ⊗ₜ w) ∧
      (∀ (σ : Gal(L/K)) (i : Γ.VertexOrbit) (a : L) (x : hObj V WK i),
        φ σ i (a • x) = σ a • φ σ i x) ∧
      -- `C2`: the cocycle condition `eq:semi-linearactiononrep`
      (∀ (σ τ : Gal(L/K)) (i : Γ.VertexOrbit) (x : hObj V WK i),
        φ σ i (φ τ i x) = φ (σ * τ) i x) ∧
      -- `C3`: continuity of the `G`-action on `⊔_v M(v)`
      (∀ x : Σ v : Γ.V, hObj V WK (Γ.vertexClass v),
        IsOpen {σ : Gal(L/K) | (⟨σ • x.1,
          hObjCast V WK (vertexClass_smul σ x.1).symm (φ σ (Γ.vertexClass x.1) x.2)⟩ :
          Σ v : Γ.V, hObj V WK (Γ.vertexClass v)) = x}) ∧
      -- `C4`: `W_{i,K} ⊗_K L_i ≅ W_i`
      (∀ i : Γ.VertexOrbit,
        Nonempty ((Γ.toSpecies.L i) ⊗[K] ↥(WK i) ≃ₗ[(Γ.toSpecies.L i)] V.W i)) ∧
      -- `C5`, `C6`: `eq:WiiMjL2`, with a **direct sum** over `η`
      (∀ i j : Γ.VertexOrbit,
        Nonempty (Balanced K (Γ.toSpecies.L j) L L
            (EtaleSpecies.Rep.tensor Γ.toSpecies i j (V.W i))
          ≃ₗ[L] ⨁ ε : Γ.EdgeOrbit i j,
            ⨁ _η : EdgeChoice.CosetIndex Γ (ch i j ε), hObj V WK i)) :=
  ⟨hPhi V WK, fun _ _ _ _ => rfl, hPhi_smul V WK, hPhi_comp V WK, hPhi_isOpen V WK,
    fun k => nonempty_baseChange_of_isKRationalStructure (hWK k),
    fun k l => wiiMjL2_nonempty V k l WK hWK ch⟩

/-! ### `RQ2-2.28` — the cocycle identity, and `H` as a functor

**Clauses `C1` and `C4` are discharged structurally — but only because `φ_e` is pinned.**
`φ_e` being `L`-linear (`C1`) and satisfying `eq:koecheractiononrep` (`C4`) are the `φEdge` and
`edge_equivariance` **fields** of `RationalQuiver.Rep`, so producing `H.obj V` as an object of
`Rep(Γ_K)` establishes both.

That argument is sound *only when the object's `φEdge` is itself pinned to be the paper's `φ_e`*,
and in the first version of this row it was not — finding **V-S5b-3**.  `φEdge := 0` satisfies both
fields (`edge_equivariance` holds because `t(σe) = σ · t(e)` in a rational quiver), so a degenerate
`H` satisfied the whole existential and the by-type discharge was empty.  The conjunct below now
pins `φ_e`, and with it the discharge is real.

The asymmetry with `RQ2-2.26` was the tell: the `F` side pinned its structure maps (`RQ2-2.26-C1`)
and the `H` side did not.  The repair states `H2`(a) in exactly the mirror shape.
-/

/-! ### `e_fix`'s core — `W_i ≅ (L ⊗_{L_i} W_i)^{G_{v_i}}`  (G4)

`e_fix` identifies `(H.obj V)(v_i)^{G_{v_i}}` with `V.W i`, and the identification is **not a
choice**: `H2`(a) constrains it, so it has to be constructed from the same `C4`/descent data as
`φ_e`.  The construction is S0's own — `RQ2-1.13` applied over the base `L_i` rather than `K`:

  `W_i  ≅  (L ⊗_{L_i} W_i)^{Gal(L/L_i)}`   (`Descent.descentUnit_bijective`).

`IsGalois ↥(Γ.vertexOrbitField i) L` is found by inference (the same fact `RQ2-2.19` runs on), and
`hObjEquivBaseChange` above puts `M(v_i)` into the `L ⊗_{L_i} W_i` form the statement wants.  That
is **design decision `D1` paying a second time**: S0's descent was built once and is consumed here
at a base it was never specialised to.

The one thing needed beyond inference is a head bridge — `S5-F3` again, in its smallest form.

@census none (G4 engine for `RQ2-2.28`)
-/

/-- `W_i` over `L_i` at the `vertexOrbitField` head.  @census none (helper, `S5-F3`) -/
noncomputable instance moduleVOFi_W (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit) :
    Module ↥(Γ.vertexOrbitField i) (V.W i) :=
  inferInstanceAs (Module (Γ.toSpecies.L i) _)

/-- **`e_fix`'s core**: `W_i ≅ (L ⊗_{L_i} W_i)^{Gal(L/L_i)}`, S0's `RQ2-1.13` over the base `L_i`.
@census none (helper for `RQ2-2.28`) -/
noncomputable def wFixedDescent (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit) :
    (V.W i) ≃ₗ[↥(Γ.vertexOrbitField i)]
      ↥(Descent.fixedPoints ↥(Γ.vertexOrbitField i) L
        ((Descent.baseChangeFunctor ↥(Γ.vertexOrbitField i) L).obj
          (ModuleCat.of _ (V.W i)))) :=
  LinearEquiv.ofBijective
    (Descent.descentUnit ↥(Γ.vertexOrbitField i) L (ModuleCat.of _ (V.W i)))
    (Descent.descentUnit_bijective ↥(Γ.vertexOrbitField i) L (ModuleCat.of _ (V.W i)))

/-! ### `RQ2-2.28`'s `φ_e` — the displayed composite  (G4)

The source defines `H.obj V`'s edge maps as *"the displayed composite through `eq:WiiMjL2` and
`f_{ij} ⊗ 1_L`"*.  Compiled, that is

```
M(v_i) --lof (ε,η)--> ⊕_ε ⊕_η M(v_i) --wiiMjL2Equiv⁻¹--> W_i ⊗_{L_i} {}_iM_j ⊗_{L_j} L
       --f'_{ij} ⊗ 1--> W_j ⊗_{L_j} L --balancedKRat--> M(v_j)
```

and every arrow is `L`-linear.  Three pieces are new:

* `balancedKRat` — `W_j ⊗_{L_j} L ≅ M(v_j)` **through clause `C4`** rather than through Galois
  descent.  It is `vertexDescentBalanced`'s mirror on the `H` side: there the identification comes
  from `RQ2-1.13`, here from the chosen `K`-rational structure;
* `fPrimeBaseChange` — `f'_{ij} ⊗ 1_L`.  `Balanced.map` is `Lᵐᵒᵖ`-linear, and the upgrade is two
  applications of the `S5-F7` bridge `balanced_smul_L_eq_op`, one per carrier;
* `phiEdgeBlock`/`phiEdgeAt` — the composite, and its restriction to one `(ε,η)`-summand.

**`RQ2-2.27-C5` landing on `M(v)` on the nose (§61.2) is what makes this typecheck as written.**
Had `C5` gone `RQ2-2.20`'s way, `wiiMjL2Equiv`'s codomain would have been
`⊕_ε ∏_η Twist(L(v_i), ητ_ε⁻¹σ_ε) ⊗ W_i` and every arrow here would have carried a further
identification.

@census none (G4 engine for `RQ2-2.28`)
-/

section PhiEdge
variable (V : EtaleSpecies.Rep Γ.toSpecies)
  (WK : ∀ k : Γ.VertexOrbit, Submodule K (V.W k))

/-- `L ⊗_{L_j} W_j`: the `L`- and `Lᵐᵒᵖ`-actions agree. -/
theorem tensor_smul_L_eq_op_VW (j : Γ.VertexOrbit) (c : L)
    (z : L ⊗[Γ.toSpecies.L j] (V.W j)) : c • z = MulOpposite.op c • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
      show (c • a) ⊗ₜ[Γ.toSpecies.L j] t = (MulOpposite.op c • a) ⊗ₜ _
      congr 1
      show c * a = a * c
      exact mul_comm c a
  | add p q hp hq => rw [smul_add, smul_add, hp, hq]

/-- **`M(v_i) = L ⊗_{L_i} W_i`**, the form Galois descent over `L/L_i` consumes: clause `C4`
followed by base-change cancellation. -/
noncomputable def hObjEquivBaseChange (i : Γ.VertexOrbit)
    (h : IsKRationalStructure V i (WK i)) :
    (L ⊗[Γ.toSpecies.L i] (V.W i)) ≃ₗ[L] hObj V WK i :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
      (kRatEquiv V WK h).symm).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      K (Γ.toSpecies.L i) L L ↥(WK i))

@[simp] theorem hObjEquivBaseChange_tmul (i : Γ.VertexOrbit)
    (h : IsKRationalStructure V i (WK i)) (a : L) (c : Γ.toSpecies.L i) (w : ↥(WK i)) :
    hObjEquivBaseChange V WK i h (a ⊗ₜ[Γ.toSpecies.L i] (kRatEquiv V WK h (c ⊗ₜ[K] w)))
      = (a * algebraMap (Γ.toSpecies.L i) L c) ⊗ₜ[K] w := by
  show (TensorProduct.AlgebraTensorModule.cancelBaseChange
      K (Γ.toSpecies.L i) L L ↥(WK i))
      (a ⊗ₜ[Γ.toSpecies.L i] ((kRatEquiv V WK h).symm (kRatEquiv V WK h (c ⊗ₜ[K] w))))
    = _
  rw [LinearEquiv.symm_apply_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  congr 1
  rw [Algebra.smul_def, mul_comm]

/-- **`W_j ⊗_{L_j} L ≅ M(v_j)`, through clause `C4`** rather than through Galois descent:
the `RQ2-2.28`-side analogue of `vertexDescentBalanced`. -/
noncomputable def balancedKRat (j : Γ.VertexOrbit)
    (h : IsKRationalStructure V j (WK j)) :
    Balanced K (Γ.toSpecies.L j) L L (V.W j) ≃ₗ[L] hObj V WK j :=
  (AddEquiv.toLinearEquiv
      (Balanced.equivTensor (K := K) (A := Γ.toSpecies.L j) (B := L)
        (X := V.W j) (fun _ _ => rfl)).toAddEquiv
      (fun c x => by
        exact (congrArg (Balanced.equivTensor (K := K) (A := Γ.toSpecies.L j) (B := L)
              (X := V.W j) (fun _ _ => rfl)).toAddEquiv
            (balanced_smul_L_eq_op (Γ.toSpecies.L j) (V.W j) c x)).trans
          (((Balanced.equivTensor (K := K) (A := Γ.toSpecies.L j) (B := L)
              (X := V.W j) (fun _ _ => rfl)).map_smul (MulOpposite.op c) x).trans
            (tensor_smul_L_eq_op_VW V j c _).symm))).trans
    (hObjEquivBaseChange V WK j h)

/-- `f'_{ij} ⊗ 1_L`, as an `L`-linear map.  `Balanced.map` is `Lᵐᵒᵖ`-linear; the upgrade is two
applications of the `S5-F7` bridge `balanced_smul_L_eq_op`, on the two carriers. -/
noncomputable def fPrimeBaseChange (i j : Γ.VertexOrbit) :
    Balanced K (Γ.toSpecies.L j) L L (EtaleSpecies.Rep.tensor Γ.toSpecies i j (V.W i))
      →ₗ[L] Balanced K (Γ.toSpecies.L j) L L (V.W j) where
  toFun := Balanced.map (K := K) (A := Γ.toSpecies.L j)
    (fun c x => Balanced.smul_K (A := Γ.toSpecies.L i) c x)
    (V.smul_K_W j) (EtaleSpecies.Rep.f' Γ.toSpecies V i j) L
  map_add' := map_add _
  map_smul' c z := by
    show Balanced.map _ _ _ L (c • z) = c • Balanced.map _ _ _ L z
    rw [balanced_smul_L_eq_op (Γ.toSpecies.L j)
        (EtaleSpecies.Rep.tensor Γ.toSpecies i j (V.W i)) c z,
      map_smul, ← balanced_smul_L_eq_op (Γ.toSpecies.L j) (V.W j) c]

/-- **`φ_e`'s block form**: `⊕_ε ⊕_η M(v_i) → M(v_j)`, the source's *"displayed composite through
`eq:WiiMjL2` and `f_{ij} ⊗ 1_L`"*. -/
noncomputable def phiEdgeBlock (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (i j : Γ.VertexOrbit)
    [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch i j ε))] :
    (⨁ ε : Γ.EdgeOrbit i j, ⨁ _η : EdgeChoice.CosetIndex Γ (ch i j ε), hObj V WK i)
      →ₗ[L] hObj V WK j :=
  (balancedKRat V WK j (hWK j)).toLinearMap ∘ₗ fPrimeBaseChange V i j ∘ₗ
    (wiiMjL2Equiv V i j WK hWK ch).symm.toLinearMap

/-- …and its restriction to one `(ε,η)`-summand, which is `φ_e` for the corresponding edge. -/
noncomputable def phiEdgeAt (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (i j : Γ.VertexOrbit)
    [Fintype (Γ.EdgeOrbit i j)] [DecidableEq (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch i j ε))]
    [∀ ε : Γ.EdgeOrbit i j, DecidableEq (EdgeChoice.CosetIndex Γ (ch i j ε))]
    (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch i j ε)) :
    hObj V WK i →ₗ[L] hObj V WK j :=
  phiEdgeBlock V WK hWK ch i j ∘ₗ
    (DirectSum.lof L (Γ.EdgeOrbit i j)
      (fun ε => ⨁ _η : EdgeChoice.CosetIndex Γ (ch i j ε), hObj V WK i) ε) ∘ₗ
    (DirectSum.lof L (EdgeChoice.CosetIndex Γ (ch i j ε))
      (fun _ => hObj V WK i) η)

end PhiEdge

/-! ### Route (C)'s Claim 2 — the `G_{v_j}`-action, and the half of `φ_e` that intertwines it  (G4)

Route (C) (§62.6) proves `hfix` by characterising the conjugated action **forwards**, never
inverting `wiiMjL2Equiv`.  It has two halves.  This section is the second one, and it is the one
that needs no chain at all:

```
balancedKRat ∘ (f' ⊗ 1_L) ∘ balAct h  =  hPhi h ∘ balancedKRat ∘ (f' ⊗ 1_L)
```

`balAct h` is `h` acting on the `L`-factor of `X ⊗_{L_j} L`.  It is well defined exactly because
`h ∈ G_{v_j}` fixes `L_j` pointwise — which is `galLinearVOF`, `h` read as an `L_j`-linear
endomorphism of `L` — and then it is `Balanced.equivTensor` conjugating mathlib's `rTensor`.
Note it is only an **`AddMonoidHom`**: `h`-semi-linearity is the whole point, so it cannot be
`Lᵐᵒᵖ`-linear, and `Balanced.hom_ext` (which is `Lᵐᵒᵖ`-linear) does not apply.  `balanced_addHom_ext`
is its additive twin.

The two halves then commute for opposite reasons: `f' ⊗ 1_L` acts on the *other* factor, so it
commutes with `balAct` **by `rfl` on generators**; and `balancedKRat` intertwines because
`hObjEquivBaseChange` does, which is again `h` fixing `L_j` — the same fact a third time.

`phiEdgeBlock_balAct` is the packaged form, and the point of its proof is that
`wiiMjL2Equiv.symm ∘ wiiMjL2Equiv` **cancels**: the chain is never computed, only cancelled.

@census none (G4 engine for `RQ2-2.28`)
-/

section BalAct
variable (V : EtaleSpecies.Rep Γ.toSpecies)
  (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i))

/-- `h ∈ G_{v_j}` as an `L_j`-linear endomorphism of `L`. -/
noncomputable def galLinearVOF (j : Γ.VertexOrbit) (h : Gal(L/K))
    (hh : h • Γ.vertexRep j = Γ.vertexRep j) : L →ₗ[Γ.toSpecies.L j] L where
  toFun := h
  map_add' _ _ := h.map_add _ _
  map_smul' c y := by
    show h ((algebraMap (Γ.toSpecies.L j) L c) • y) = (algebraMap (Γ.toSpecies.L j) L c) • h y
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    exact (IntermediateField.mem_fixedField_iff _ _).mp c.2 h hh

section GenericCarrier
variable {X : Type u} [AddCommGroup X] [Module K X]

/-- **The `G_{v_j}`-action on `X ⊗_{L_j} L`**: `h` on the `L`-factor.  Well defined because `h`
fixes `L_j`, which is exactly `galLinearVOF`. -/
noncomputable def balAct (j : Γ.VertexOrbit) [Module (Γ.toSpecies.L j)ᵐᵒᵖ X]
    [SMulCommClass K (Γ.toSpecies.L j)ᵐᵒᵖ X] [Module (Γ.toSpecies.L j) X]
    [IsScalarTower K (Γ.toSpecies.L j)ᵐᵒᵖ X] [IsScalarTower K (Γ.toSpecies.L j) X]
    (hX : ∀ (a : Γ.toSpecies.L j) (x : X), a • x = MulOpposite.op a • x)
    (h : Gal(L/K)) (hh : h • Γ.vertexRep j = Γ.vertexRep j) :
    Balanced K (Γ.toSpecies.L j) L L X →+ Balanced K (Γ.toSpecies.L j) L L X :=
  ((Balanced.equivTensor (B := L) hX).symm.toAddMonoidHom).comp
    (((LinearMap.rTensor X (galLinearVOF j h hh)).toAddMonoidHom).comp
      ((Balanced.equivTensor (B := L) hX).toAddMonoidHom))

@[simp] theorem balAct_mk (j : Γ.VertexOrbit) [Module (Γ.toSpecies.L j)ᵐᵒᵖ X]
    [SMulCommClass K (Γ.toSpecies.L j)ᵐᵒᵖ X] [Module (Γ.toSpecies.L j) X]
    [IsScalarTower K (Γ.toSpecies.L j)ᵐᵒᵖ X] [IsScalarTower K (Γ.toSpecies.L j) X]
    (hX : ∀ (a : Γ.toSpecies.L j) (x : X), a • x = MulOpposite.op a • x)
    (h : Gal(L/K)) (hh : h • Γ.vertexRep j = Γ.vertexRep j) (x : X) (y : L) :
    balAct j hX h hh (Balanced.mk (K := K) (A := Γ.toSpecies.L j) (B := L) x y)
      = Balanced.mk x (h y) := by
  show (Balanced.equivTensor (B := L) hX).symm (LinearMap.rTensor X (galLinearVOF j h hh)
      ((Balanced.equivTensor (B := L) hX) (Balanced.mk x y))) = _
  rw [Balanced.equivTensor_mk, LinearMap.rTensor_tmul]
  exact Balanced.equivTensor_symm_tmul hX _ _

theorem hObjEquivBaseChange_gal (j : Γ.VertexOrbit)
    (hj : IsKRationalStructure V j (WK j)) (h : Gal(L/K))
    (hh : h • Γ.vertexRep j = Γ.vertexRep j)
    (z : L ⊗[Γ.toSpecies.L j] (V.W j)) :
    hObjEquivBaseChange V WK j hj (LinearMap.rTensor (V.W j) (galLinearVOF j h hh) z)
      = hPhi V WK h j (hObjEquivBaseChange V WK j hj z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
      obtain ⟨t, rfl⟩ : ∃ t, kRatEquiv V WK hj t = y :=
        ⟨(kRatEquiv V WK hj).symm y, LinearEquiv.apply_symm_apply _ _⟩
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero, TensorProduct.tmul_zero]; simp
      | tmul c w =>
          rw [LinearMap.rTensor_tmul]
          show hObjEquivBaseChange V WK j hj ((h a) ⊗ₜ[Γ.toSpecies.L j] _) = _
          rw [hObjEquivBaseChange_tmul, hObjEquivBaseChange_tmul, hPhi_tmul]
          congr 1
          rw [map_mul]
          congr 1
          exact ((IntermediateField.mem_fixedField_iff _ _).mp c.2 h hh).symm
      | add p q hp hq =>
          rw [map_add, TensorProduct.tmul_add, map_add, map_add, map_add, map_add, hp, hq]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

end GenericCarrier

/-- Additive maps out of a `Balanced` agree if they agree on pure tensors. -/
theorem balanced_addHom_ext {A B Y X0 Z : Type u} [Ring A] [Algebra K A] [Ring B]
    [AddCommGroup Y] [Module K Y] [Module A Y] [Module Bᵐᵒᵖ Y] [IsScalarTower K A Y]
    [SMulCommClass K Bᵐᵒᵖ Y] [SMulCommClass A Bᵐᵒᵖ Y]
    [AddCommGroup X0] [Module K X0] [Module Aᵐᵒᵖ X0] [IsScalarTower K Aᵐᵒᵖ X0]
    [AddCommGroup Z]
    {g h : Balanced K A B Y X0 →+ Z}
    (H : ∀ (x : X0) (y : Y), g (Balanced.mk x y) = h (Balanced.mk x y)) : g = h := by
  refine AddMonoidHom.ext fun t => ?_
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K A B Y X0) t
  induction s with
  | zero => rw [show (Submodule.Quotient.mk (0 : Y ⊗[K] X0) :
      Balanced K A B Y X0) = 0 from rfl, map_zero, map_zero]
  | tmul y x => exact H x y
  | add s t hs ht =>
      have hmk : (Submodule.Quotient.mk (s + t) : Balanced K A B Y X0)
          = Submodule.Quotient.mk s + Submodule.Quotient.mk t := rfl
      rw [hmk, map_add, map_add, hs, ht]

/-- `balancedKRat` intertwines `balAct` with `hPhi`. -/
theorem balancedKRat_balAct (j : Γ.VertexOrbit) (hj : IsKRationalStructure V j (WK j))
    (h : Gal(L/K)) (hh : h • Γ.vertexRep j = Γ.vertexRep j)
    (z : Balanced K (Γ.toSpecies.L j) L L (V.W j)) :
    balancedKRat V WK j hj (balAct j (fun _ _ => rfl) h hh z)
      = hPhi V WK h j (balancedKRat V WK j hj z) := by
  show hObjEquivBaseChange V WK j hj (Balanced.equivTensor (B := L) (fun _ _ => rfl)
      ((Balanced.equivTensor (B := L) (fun _ _ => rfl)).symm
        (LinearMap.rTensor (V.W j) (galLinearVOF j h hh)
          (Balanced.equivTensor (B := L) (fun _ _ => rfl) z)))) = _
  rw [LinearEquiv.apply_symm_apply, hObjEquivBaseChange_gal]
  rfl

/-- `f' ⊗ 1_L` commutes with `balAct` — it acts on the other factor. -/
theorem fPrimeBaseChange_balAct (i j : Γ.VertexOrbit)
    (h : Gal(L/K)) (hh : h • Γ.vertexRep j = Γ.vertexRep j)
    (z : Balanced K (Γ.toSpecies.L j) L L
      (EtaleSpecies.Rep.tensor Γ.toSpecies i j (V.W i))) :
    fPrimeBaseChange V i j (balAct j (fun _ _ => rfl) h hh z)
      = balAct j (fun _ _ => rfl) h hh (fPrimeBaseChange V i j z) := by
  have key : ((fPrimeBaseChange V i j).toAddMonoidHom.comp
        (balAct j (fun _ _ => rfl) h hh))
      = ((balAct j (fun _ _ => rfl) h hh).comp
        (fPrimeBaseChange V i j).toAddMonoidHom) := by
    refine balanced_addHom_ext fun x y => ?_
    rfl
  exact DFunLike.congr_fun key z

/-- **Claim 2 of route (C)**: the `f' ⊗ 1_L` half of `φ_e` intertwines `balAct` with `hPhi`.
Note this is `phiEdgeBlock ∘ wiiMjL2Equiv` — the chain is *cancelled*, not inverted. -/
theorem edgeBlockCore_balAct (i j : Γ.VertexOrbit) (hj : IsKRationalStructure V j (WK j))
    (h : Gal(L/K)) (hh : h • Γ.vertexRep j = Γ.vertexRep j)
    (z : Balanced K (Γ.toSpecies.L j) L L
      (EtaleSpecies.Rep.tensor Γ.toSpecies i j (V.W i))) :
    balancedKRat V WK j hj (fPrimeBaseChange V i j (balAct j (fun _ _ => rfl) h hh z))
      = hPhi V WK h j (balancedKRat V WK j hj (fPrimeBaseChange V i j z)) := by
  rw [fPrimeBaseChange_balAct, balancedKRat_balAct]

open scoped Classical in
/-- …stated against `phiEdgeBlock` itself, with `wiiMjL2Equiv` cancelling. -/
theorem phiEdgeBlock_balAct
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (i j : Γ.VertexOrbit)
    [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch i j ε))]
    (h : Gal(L/K)) (hh : h • Γ.vertexRep j = Γ.vertexRep j)
    (z : Balanced K (Γ.toSpecies.L j) L L
      (EtaleSpecies.Rep.tensor Γ.toSpecies i j (V.W i))) :
    phiEdgeBlock V WK hWK ch i j
        (wiiMjL2Equiv V i j WK hWK ch (balAct j (fun _ _ => rfl) h hh z))
      = hPhi V WK h j (phiEdgeBlock V WK hWK ch i j (wiiMjL2Equiv V i j WK hWK ch z)) := by
  show balancedKRat V WK j (hWK j) (fPrimeBaseChange V i j
      ((wiiMjL2Equiv V i j WK hWK ch).symm
        (wiiMjL2Equiv V i j WK hWK ch (balAct j (fun _ _ => rfl) h hh z)))) = _
  rw [LinearEquiv.symm_apply_apply]
  show _ = hPhi V WK h j (balancedKRat V WK j (hWK j) (fPrimeBaseChange V i j
      ((wiiMjL2Equiv V i j WK hWK ch).symm (wiiMjL2Equiv V i j WK hWK ch z))))
  rw [LinearEquiv.symm_apply_apply]
  exact edgeBlockCore_balAct V WK i j (hWK j) h hh z

end BalAct

/-- The base coset of `G_{v_j}/G_{τ_ε^{-1}e_ε}`.  `CosetIndex` is a coset *space*, not a group, so
this is `QuotientGroup.mk 1` and not the numeral.  @census none (helper) -/
noncomputable def EdgeChoice.cosetOne {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε) :
    EdgeChoice.CosetIndex Γ ch := QuotientGroup.mk 1

open scoped Classical in
/-- The translation `η₀ τ_ε^{-1}` conjugating `G_{e_ε}` to the stabiliser of the `η₀`-indexed edge.
@census none (helper) -/
noncomputable def EdgeChoice.baseTrans {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) : Gal(L/K) :=
  EdgeChoice.rep Γ ch (EdgeChoice.cosetOne ch) * ch.τ⁻¹

/-- The stabiliser of an edge translated to sit at `v_j` lies in `G_{v_j}`: `G_e ≤ G_{t(e)}`
(`stabilizer_le_target`) with `t(ρ e_ε) = v_j` (`EdgeChoice.cosetTarget`).  This is what makes the
`L_j`-part `G_{e}`-fixed, and hence the whole equivariance argument go through.
@census none (helper) -/
theorem cosetTrans_stabilizer_le {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch) {k : Gal(L/K)}
    (hk : k • Γ.edgeRep ε = Γ.edgeRep ε) :
    ((EdgeChoice.rep Γ ch η * ch.τ⁻¹) * k * (EdgeChoice.rep Γ ch η * ch.τ⁻¹)⁻¹)
      • Γ.vertexRep j = Γ.vertexRep j := by
  set ρ := EdgeChoice.rep Γ ch η * ch.τ⁻¹ with hρ
  have hstab : (ρ * k * ρ⁻¹) • (ρ • Γ.edgeRep ε) = ρ • Γ.edgeRep ε := by
    rw [← mul_smul]
    have hg : ρ * k * ρ⁻¹ * ρ = ρ * k := by group
    rw [hg, mul_smul, hk]
  have hle := Γ.stabilizer_le_target (ρ • Γ.edgeRep ε) (x := ρ * k * ρ⁻¹) hstab
  rwa [Γ.target_smul, ch.cosetTarget η] at hle

/-! ### Route (C)'s Claim 1 — the chain pin, `A_h`, and `hfix`  (G4)

The first half of route (C), and the one that does need the chain.  Three steps.

**The pin** (`wiiMjL2Equiv_apply`) mirrors the `F` side's `wiiMjPreChain_apply` link for link, and
closes in two tactic steps once the two `Balanced` generators are in place — the second of which is
`RQ2-2.20-C1`'s pin arriving through `.choose_spec` (§62.5).  Everything after it is computation on
generators.

**`A_h`** (`wiiMjL2Equiv_balAct`) is the conjugated action, characterised **forwards**:

```
wiiMjL2Equiv (balAct h z) ε (σ · η)  =  hPhi h (wiiMjL2Equiv z ε η),      σ = ⟨h, hh⟩ ∈ G_{v_j}.
```

So `balAct h` acts on `⊕_ε ⊕_η M(v_i)` by **permuting the coset index and applying `hPhi h`** —
which is exactly the shape the `F` side hypothesised for its `Θ'` in `phiTotal_equivariant`, now
supplied rather than assumed.  Its scalar content is `EdgeChoice.smul_twist_apply`: `σ` carries the
twist `ητ_ε^{-1}` to `(σ·η)τ_ε^{-1}` on `L(e_ε)`.  That lemma was proved for `RQ2-2.24` and is
reused here verbatim — the `H` side's mirror of `RQ2-2.24-C1` needs precisely the same fact.

**`hfix`** (`phiEdgeAt_fixed`) then falls out.  With `h = ρ k ρ^{-1}` for `k ∈ G_{e_ε}`:
`h` fixes the base coset `η₀` (`baseTrans_conj_smul_cosetOne`, whose only input is that `rep η₀`
stabilises `τ_ε^{-1}e_ε` — because `η₀` *is* the identity coset), so `A_h` fixes the `(ε,η₀)`
summand, so `balAct h` fixes its preimage, and Claim 2 (§62.7) carries that through
`f' ⊗ 1_L` to the conclusion.  **`wiiMjL2Equiv.symm` is applied to nothing and computed nowhere**;
it appears only as `LinearEquiv.apply_symm_apply`.

@census none (G4 engine for `RQ2-2.28`; clause witness `RQ2-2.28-C2`)
-/

section Claim1
variable (V : EtaleSpecies.Rep Γ.toSpecies) {i j : Γ.VertexOrbit}

open scoped Classical in
/-- **The `H`-side chain pin**, mirroring `wiiMjPreChain_apply`. -/
theorem wiiMjL2Equiv_apply
    (WK : ∀ k : Γ.VertexOrbit, Submodule K (V.W k))
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch i j ε))]
    (w : V.W i) (m : Γ.toSpecies.M i j) (a : L)
    (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch i j ε)) :
    wiiMjL2Equiv V i j WK hWK ch (Balanced.mk (Balanced.mk w m) a) ε η
      = wiiMjL2Summand V WK ε
          (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹) (hWK i)
          (Twist.ofL a ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε)
              (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹)]
            edgeSummandMkG (V.W i) ε (m ε) w) := by
  have h0 : (outerEquivL i j (V.W i)) (Balanced.mk (Balanced.mk w m) a)
      = a ⊗ₜ[↥(Γ.vertexOrbitField j)]
          (Balanced.mk w m : EtaleSpecies.Rep.tensor Γ.toSpecies i j _) := rfl
  have h1 : ((innerEquivH V i j).trans (piSplitVOFH V i j))
      (Balanced.mk w m : EtaleSpecies.Rep.tensor Γ.toSpecies i j _)
      = fun ε => edgeSummandMkG (V.W i) ε (m ε) w := by
    funext ε'
    show piSplitH V i j (m ⊗ₜ[Γ.toSpecies.L i] w) ε' = _
    rw [piSplitH_tmul]
    rfl
  simp only [wiiMjL2Equiv, LinearEquiv.trans_apply, h0,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, h1,
    TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  show wiiMjL2Summand V WK ε
      (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹) (hWK i)
      ((leEpsilon_at_edgeSummandG (V.W i) (ch i j ε)).choose
        (a ⊗ₜ[↥(Γ.vertexOrbitField j)] edgeSummandMkG (V.W i) ε (m ε) w) η) = _
  rw [(leEpsilon_at_edgeSummandG (V.W i) (ch i j ε)).choose_spec a
    (edgeSummandMkG (V.W i) ε (m ε) w) η]



section Claim1Theta
variable (WK : ∀ k : Γ.VertexOrbit, Submodule K (V.W k))

/-- `wiiMjL2Summand` on a `Twist.ofL` generator, before the twist is absorbed. -/
theorem wiiMjL2Summand_ofL {i : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) (ρ : Gal(L/K))
    (hi : IsKRationalStructure V i (WK i)) (b : L) (v : edgeSummandG (V.W i) ε) :
    wiiMjL2Summand V WK ε ρ hi
        (Twist.ofL b ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] v)
      = twistAbsorb (Γ.edgeOrbitField ε) ρ ↥(WK i)
          (Twist.ofL b ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ]
            (edgeSummandKRat V WK ε hi v)) := rfl

/-- Moving `hPhi h` across `twistAbsorb` changes the twist from `ρ` to `ρ'` — provided `h ∘ ρ = ρ'`
on `E`.  This is the scalar half of the equivariance. -/
theorem hPhi_twistAbsorb {E : IntermediateField K L} {ρ ρ' : Gal(L/K)} (h : Gal(L/K))
    (hcomp : ∀ x : ↥E, h (ρ (x : L)) = ρ' (x : L))
    (i : Γ.VertexOrbit) (b : L) (y : ↥E ⊗[K] ↥(WK i)) :
    hPhi V WK h i (twistAbsorb E ρ ↥(WK i)
        (Twist.ofL b ⊗ₜ[Twist.TwistBase E ρ] y))
      = twistAbsorb E ρ' ↥(WK i)
          (Twist.ofL (h b) ⊗ₜ[Twist.TwistBase E ρ'] y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, TensorProduct.tmul_zero, map_zero, map_zero, map_zero]
  | tmul x w =>
      rw [twistAbsorb_tmul, twistAbsorb_tmul, hPhi_tmul]
      show (h (b * ρ (x : L))) ⊗ₜ[K] w = _
      rw [map_mul, hcomp x]
  | add p q hp hq =>
      rw [TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, map_add, map_add, hp, hq]

open scoped Classical in
/-- **`A_h`**: `balAct h` acts on `⊕_ε ⊕_η M(v_i)` by permuting `η` and applying `hPhi h`. -/
theorem wiiMjL2Equiv_balAct {i : Γ.VertexOrbit}
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch i j ε))]
    (h : Gal(L/K)) (hh : h • Γ.vertexRep j = Γ.vertexRep j)
    (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch i j ε))
    (z : Balanced K (Γ.toSpecies.L j) L L
      (EtaleSpecies.Rep.tensor Γ.toSpecies i j (V.W i))) :
    wiiMjL2Equiv V i j WK hWK ch (balAct j (fun _ _ => rfl) h hh z) ε
        ((⟨h, hh⟩ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) • η)
      = hPhi V WK h i (wiiMjL2Equiv V i j WK hWK ch z ε η) := by
  have key : (((DFinsupp.evalAddMonoidHom
        ((⟨h, hh⟩ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) • η)).comp
          ((DFinsupp.evalAddMonoidHom ε).comp
            ((wiiMjL2Equiv V i j WK hWK ch).toLinearMap.toAddMonoidHom.comp
              (balAct j (fun _ _ => rfl) h hh))))
      = (((hPhi V WK h i).toAddMonoidHom).comp
          (((DFinsupp.evalAddMonoidHom η).comp
            ((DFinsupp.evalAddMonoidHom ε).comp
              (wiiMjL2Equiv V i j WK hWK ch).toLinearMap.toAddMonoidHom))))) := by
    refine balanced_addHom_ext fun t a => ?_
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective
      (balancedRel K (Γ.toSpecies.L i) (Γ.toSpecies.L j) (Γ.toSpecies.M i j) (V.W i)) t
    induction s with
    | zero =>
        rw [show (Submodule.Quotient.mk (0 : Γ.toSpecies.M i j ⊗[K] V.W i) :
          EtaleSpecies.Rep.tensor Γ.toSpecies i j (V.W i)) = 0 from rfl]
        rw [show Balanced.mk (K := K) (A := Γ.toSpecies.L j) (B := L)
          (0 : EtaleSpecies.Rep.tensor Γ.toSpecies i j (V.W i)) a = 0 from
          Balanced.mk_zero_left a]
        simp
    | tmul m w =>
        show _ = _
        rw [show (Submodule.Quotient.mk (m ⊗ₜ[K] w) :
          EtaleSpecies.Rep.tensor Γ.toSpecies i j (V.W i)) = Balanced.mk w m from rfl]
        show wiiMjL2Equiv V i j WK hWK ch
            (balAct j (fun _ _ => rfl) h hh (Balanced.mk (Balanced.mk w m) a)) ε _ = _
        rw [balAct_mk, wiiMjL2Equiv_apply, wiiMjL2Summand_ofL]
        show _ = hPhi V WK h i (wiiMjL2Equiv V i j WK hWK ch
          (Balanced.mk (Balanced.mk w m) a) ε η)
        rw [wiiMjL2Equiv_apply, wiiMjL2Summand_ofL,
          hPhi_twistAbsorb V WK h
            (EdgeChoice.smul_twist_apply (ch i j ε) ⟨h, hh⟩ η) i a _]
    | add s t hs ht =>
        rw [show (Submodule.Quotient.mk (s + t) :
          EtaleSpecies.Rep.tensor Γ.toSpecies i j (V.W i))
            = Submodule.Quotient.mk s + Submodule.Quotient.mk t from rfl,
          Balanced.mk_add_left, map_add, map_add, hs, ht]
  exact DFunLike.congr_fun key z

/-- `rep η₀` stabilises `τ_ε⁻¹ e_ε` — `η₀` is the identity coset. -/
theorem EdgeChoice.rep_cosetOne_mem {i : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) :
    EdgeChoice.rep Γ ch (EdgeChoice.cosetOne ch) ∈
      stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε) := by
  have h := Quotient.out_eq (EdgeChoice.cosetOne (Γ := Γ) ch)
  have h2 : (QuotientGroup.mk (Quotient.out (EdgeChoice.cosetOne (Γ := Γ) ch))
      : EdgeChoice.CosetIndex Γ ch) = QuotientGroup.mk 1 := h
  rw [QuotientGroup.eq, mul_one] at h2
  have hinv : (EdgeChoice.rep Γ ch (EdgeChoice.cosetOne ch))⁻¹
      ∈ stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε) := h2
  simpa using inv_mem hinv

/-- The conjugate `ρ k ρ⁻¹` of an edge-stabiliser element fixes the base coset `η₀`. -/
theorem baseTrans_conj_smul_cosetOne {i : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) {k : Gal(L/K)} (hk : k • Γ.edgeRep ε = Γ.edgeRep ε)
    (hh : (ch.baseTrans * k * ch.baseTrans⁻¹) • Γ.vertexRep j = Γ.vertexRep j) :
    (⟨ch.baseTrans * k * ch.baseTrans⁻¹, hh⟩ :
        ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) • EdgeChoice.cosetOne ch
      = EdgeChoice.cosetOne ch := by
  have hr : EdgeChoice.rep Γ ch (EdgeChoice.cosetOne ch)
      ∈ stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε) := EdgeChoice.rep_cosetOne_mem ch
  have hrinv : (EdgeChoice.rep Γ ch (EdgeChoice.cosetOne ch))⁻¹
      ∈ stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε) := inv_mem hr
  -- `ρ k ρ⁻¹` stabilises `τ⁻¹ e_ε`
  have hstab : (ch.baseTrans * k * ch.baseTrans⁻¹) • (ch.τ⁻¹ • Γ.edgeRep ε)
      = ch.τ⁻¹ • Γ.edgeRep ε := by
    show (EdgeChoice.rep Γ ch (EdgeChoice.cosetOne ch) * ch.τ⁻¹ * k *
      (EdgeChoice.rep Γ ch (EdgeChoice.cosetOne ch) * ch.τ⁻¹)⁻¹) • _ = _
    rw [mul_inv_rev, inv_inv]
    rw [mul_smul, mul_smul, mul_smul, mul_smul]
    rw [show (EdgeChoice.rep Γ ch (EdgeChoice.cosetOne ch))⁻¹ • (ch.τ⁻¹ • Γ.edgeRep ε)
        = ch.τ⁻¹ • Γ.edgeRep ε from hrinv]
    rw [smul_smul ch.τ ch.τ⁻¹, mul_inv_cancel, one_smul, hk]
    exact hr
  show QuotientGroup.mk _ = QuotientGroup.mk (1 : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)))
  rw [QuotientGroup.eq, mul_one]
  exact inv_mem hstab

open scoped Classical in
/-- **`hfix`** — the fixed-field statement `phiEdgeRep_equivariant` was reduced to. -/
theorem phiEdgeAt_fixed {i : Γ.VertexOrbit}
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    [Fintype (Γ.EdgeOrbit i j)] [DecidableEq (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch i j ε))]
    [∀ ε : Γ.EdgeOrbit i j, DecidableEq (EdgeChoice.CosetIndex Γ (ch i j ε))]
    (ε : Γ.EdgeOrbit i j) (k : Gal(L/K)) (hk : k • Γ.edgeRep ε = Γ.edgeRep ε)
    (w : ↥(WK i)) :
    hPhi V WK ((ch i j ε).baseTrans * k * (ch i j ε).baseTrans⁻¹) j
        (phiEdgeAt V WK hWK ch i j ε (EdgeChoice.cosetOne (ch i j ε)) ((1 : L) ⊗ₜ[K] w))
      = phiEdgeAt V WK hWK ch i j ε (EdgeChoice.cosetOne (ch i j ε)) ((1 : L) ⊗ₜ[K] w) := by
  have hh : ((ch i j ε).baseTrans * k * (ch i j ε).baseTrans⁻¹) • Γ.vertexRep j
      = Γ.vertexRep j :=
    cosetTrans_stabilizer_le (ch i j ε) (EdgeChoice.cosetOne (ch i j ε)) hk
  set σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)) :=
    ⟨(ch i j ε).baseTrans * k * (ch i j ε).baseTrans⁻¹, hh⟩ with hσ
  have hfixη : σ • EdgeChoice.cosetOne (ch i j ε) = EdgeChoice.cosetOne (ch i j ε) :=
    baseTrans_conj_smul_cosetOne (ch i j ε) hk hh
  set Y := DirectSum.lof L (Γ.EdgeOrbit i j)
      (fun ε => DirectSum (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj V WK i)) ε
      (DirectSum.lof L (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj V WK i)
        (EdgeChoice.cosetOne (ch i j ε)) ((1 : L) ⊗ₜ[K] w)) with hYdef
  show hPhi V WK _ j (phiEdgeBlock V WK hWK ch i j Y) = phiEdgeBlock V WK hWK ch i j Y
  set z := (wiiMjL2Equiv V i j WK hWK ch).symm Y with hzdef
  have hz : wiiMjL2Equiv V i j WK hWK ch z = Y := LinearEquiv.apply_symm_apply _ _
  rw [← hz, ← phiEdgeBlock_balAct V WK hWK ch i j _ hh z]
  congr 1
  -- Claim 1: `balAct` fixes the `(ε,η₀)`-summand's preimage
  rw [hz]
  refine DFinsupp.ext fun ε' => ?_
  refine DFinsupp.ext fun η' => ?_
  have hA := wiiMjL2Equiv_balAct V WK hWK ch
    ((ch i j ε).baseTrans * k * (ch i j ε).baseTrans⁻¹) hh ε' (σ⁻¹ • η') z
  rw [show (⟨(ch i j ε).baseTrans * k * (ch i j ε).baseTrans⁻¹, hh⟩ :
      ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) = σ from rfl, smul_inv_smul, hz] at hA
  rw [hA]
  rcases eq_or_ne ε' ε with rfl | hε
  · have h1 : Y ε' = DirectSum.lof L (EdgeChoice.CosetIndex Γ (ch i j ε'))
        (fun _ => hObj V WK i) (EdgeChoice.cosetOne (ch i j ε')) ((1 : L) ⊗ₜ[K] w) := by
      rw [hYdef, DirectSum.lof_eq_of, DirectSum.of_eq_same]
    rw [h1]
    rcases eq_or_ne η' (EdgeChoice.cosetOne (ch i j ε')) with rfl | hη
    · have h2 : σ⁻¹ • EdgeChoice.cosetOne (ch i j ε')
          = EdgeChoice.cosetOne (ch i j ε') := by
        rw [inv_smul_eq_iff]; exact hfixη.symm
      rw [h2, DirectSum.lof_eq_of, DirectSum.of_eq_same]
      show hPhi V WK _ i ((1 : L) ⊗ₜ[K] w) = _
      rw [hPhi_tmul, map_one]
    · have h3 : σ⁻¹ • η' ≠ EdgeChoice.cosetOne (ch i j ε') := by
        intro hc
        exact hη (by rw [← hfixη, ← hc, smul_inv_smul])
      rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ h3,
        DirectSum.of_eq_of_ne _ _ _ hη, map_zero]
  · have h4 : Y ε' = 0 := by
      rw [hYdef, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hε]
    rw [h4]
    have hz0 : ((0 : DirectSum (EdgeChoice.CosetIndex Γ (ch i j ε'))
        (fun _ => hObj V WK i)) (σ⁻¹ • η')) = 0 := rfl
    rw [hz0, map_zero]
    rfl

end Claim1Theta

end Claim1



/-! ### `RQ2-2.28`'s edge datum — `φ_{e_ε}`, one map per edge **orbit**  (G4)

The obvious reading of `H2`(a) is that `H.obj V`'s edge field needs the full correspondence between
edges and the `(ε,η)` index pairs of `eq:WiiMjL2` — a bijection
`E_{ij} ∩ t^{-1}(v_j) ≃ Σ_ε G_{v_j}/G_{τ_ε^{-1}e_ε}`, several hundred lines of coset bookkeeping.

**That reading is wrong, and the landed `F` side says so.**  `phiComp` is
`φ_{t(e_ε), η τ_ε^{-1}} ∘ φ_{e_ε} ∘ φ_{v_i, σ_ε}`, and the only edge it names is the orbit
*representative* `Γ.edgeRep ε`.  `Φ_{ij}` is the sum of those over `(ε,η)`, so `Φ_{ij}` depends on
`φEdge` **only at the representatives**; every other edge's map is forced by clause `RQ2-1.08-C9`
rather than being an independent datum.  The bijection is never needed (§62.2).

So the datum is one `L`-linear map per edge *orbit*, and it is built on the `K`-form:

```
φEdgeRep ε  =  φ_{η τ_ε^{-1}}^{-1} ∘ phiEdgeAt ε η ∘ φ_{σ_ε}^{-1}
```

reads as written only up to two semi-linear factors that do not cancel.  They cancel on
`1 ⊗ W_{i,K}`, because `hPhi` is `σ ⊗ 1` and is therefore the **identity on the `K`-form**; there
the composite is `K`-linear, and `LinearMap.liftBaseChange` extends it back `L`-linearly.  That is
`RQ2-2.27-H2`'s `K`-rational structure earning its keep a second time (§62.3), and it is why
`φEdgeRep` is a *definition* rather than a choice — the constraint §61's probe identified.

@census none (G4 engine for `RQ2-2.28`)
-/


section EdgeDatum
variable (V : EtaleSpecies.Rep Γ.toSpecies)
  (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i))

/-- `hPhi` is `K`-linear: `σ` fixes `K`.  @census none (helper) -/
theorem hPhi_smul_K (σ : Gal(L/K)) (i : Γ.VertexOrbit) (c : K) (x : hObj V WK i) :
    hPhi V WK σ i (c • x) = c • hPhi V WK σ i x := by
  rw [← algebraMap_smul L c x, hPhi_smul, σ.commutes, algebraMap_smul]

/-- …hence so is its inverse.  @census none (helper) -/
theorem hPhi_symm_smul_K (σ : Gal(L/K)) (i : Γ.VertexOrbit) (c : K) (y : hObj V WK i) :
    (hPhi V WK σ i).symm (c • y) = c • (hPhi V WK σ i).symm y := by
  refine (hPhi V WK σ i).injective ?_
  rw [AddEquiv.apply_symm_apply, hPhi_smul_K, AddEquiv.apply_symm_apply]

open scoped Classical in
/-- **`φ_{e_ε}` on the `K`-form** `W_{i,K}`, where the two semi-linear factors are the identity.
@census none (helper for `RQ2-2.28`) -/
noncomputable def phiEdgeRepK
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (i j : Γ.VertexOrbit)
    [Fintype (Γ.EdgeOrbit i j)] [DecidableEq (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch i j ε))]
    [∀ ε : Γ.EdgeOrbit i j, DecidableEq (EdgeChoice.CosetIndex Γ (ch i j ε))]
    (ε : Γ.EdgeOrbit i j) :
    ↥(WK i) →ₗ[K] hObj V WK j where
  toFun w := (hPhi V WK
      ((ch i j ε).baseTrans) j).symm
    (phiEdgeAt V WK hWK ch i j ε (EdgeChoice.cosetOne (ch i j ε)) ((1 : L) ⊗ₜ[K] w))
  map_add' w w' := by
    rw [TensorProduct.tmul_add, map_add, map_add]
  map_smul' c w := by
    show (hPhi V WK _ j).symm (phiEdgeAt V WK hWK ch i j ε (EdgeChoice.cosetOne (ch i j ε)) ((1 : L) ⊗ₜ[K] (c • w))) = _
    rw [TensorProduct.tmul_smul, ← algebraMap_smul L c ((1 : L) ⊗ₜ[K] w),
      LinearMap.map_smul, algebraMap_smul, hPhi_symm_smul_K]
    rfl

open scoped Classical in
/-- **`φ_{e_ε}`**: the `L`-linear extension of `phiEdgeRepK` from the `K`-form.  This is the whole
edge datum of `H.obj V` — one map per edge **orbit** (§62.2).
@census none (helper for `RQ2-2.28`) -/
noncomputable def phiEdgeRep
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (i j : Γ.VertexOrbit)
    [Fintype (Γ.EdgeOrbit i j)] [DecidableEq (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch i j ε))]
    [∀ ε : Γ.EdgeOrbit i j, DecidableEq (EdgeChoice.CosetIndex Γ (ch i j ε))]
    (ε : Γ.EdgeOrbit i j) :
    hObj V WK i →ₗ[L] hObj V WK j :=
  LinearMap.liftBaseChange L (phiEdgeRepK V WK hWK ch i j ε)

open scoped Classical in
/-- The pin: on the `K`-form, `φ_{e_ε}` is `phiEdgeAt` with its outer twist undone.
@census none (helper) -/
@[simp] theorem phiEdgeRep_tmul
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (i j : Γ.VertexOrbit)
    [Fintype (Γ.EdgeOrbit i j)] [DecidableEq (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch i j ε))]
    [∀ ε : Γ.EdgeOrbit i j, DecidableEq (EdgeChoice.CosetIndex Γ (ch i j ε))]
    (ε : Γ.EdgeOrbit i j) (a : L) (w : ↥(WK i)) :
    phiEdgeRep V WK hWK ch i j ε (a ⊗ₜ[K] w)
      = a • (hPhi V WK ((ch i j ε).baseTrans) j).symm
          (phiEdgeAt V WK hWK ch i j ε (EdgeChoice.cosetOne (ch i j ε)) ((1 : L) ⊗ₜ[K] w)) :=
  LinearMap.liftBaseChange_tmul _ _ _ _


/-- `g k g^{-1}` fixing `Z` is `k` fixing `φ_g^{-1} Z`.  @census none (helper) -/
theorem hPhi_fix_symm {j : Γ.VertexOrbit} {g k : Gal(L/K)} (Z : hObj V WK j)
    (h : hPhi V WK (g * k * g⁻¹) j Z = Z) :
    hPhi V WK k j ((hPhi V WK g j).symm Z) = (hPhi V WK g j).symm Z := by
  refine (hPhi V WK g j).injective ?_
  rw [AddEquiv.apply_symm_apply, hPhi_comp]
  have hgk : g * k = (g * k * g⁻¹) * g := by group
  rw [hgk, ← hPhi_comp, AddEquiv.apply_symm_apply, h]

open scoped Classical in
/-- **`φ_{e_ε}` is `G_{e_ε}`-equivariant, reduced to a statement about `phiEdgeAt` alone.**

This is the theorem the whole edge field rests on: it is simultaneously what makes
`φ_e := φ_{g_e} ∘ φ_{e_ε} ∘ φ_{g_e}^{-1}` independent of the choice of `g_e`, and — transported
along that formula — the `edge_equivariance` field itself (clause `RQ2-1.08-C9`).

The reduction is complete and costs nothing: both sides are `k`-semi-linear, so a tensor induction
reduces the whole statement to the `K`-form, and there `phiEdgeRep`'s two outer semi-linear factors
collapse (§62.3).  What is left is one fact, `phiEdgeAt_fixed` — proved above by route (C) — and it
is a *fixed-field* statement:
the `(ε,η₀)`-block of `f' ⊗ 1_L` must take the `K`-form into the part of `M(v_j)` fixed by
`G_{e(ε,η₀)}`.  That is the source's *"`φ_e` is defined over `L(e)`"*, and it is visible in
`twistAbsorb`'s own pin — `twistAbsorb (t ⊗ (x ⊗ w)) = (t·ρx) ⊗ w`, so the coefficient produced on
the `K`-form is `ρ(L(e_ε)) = L(ρ e_ε) = L(e(ε,η₀))`.

It was isolated as a hypothesis while the chain was unfolded, so that everything consuming the
equivariance could be built and compiled first; it is now discharged (`phiEdgeAt_fixed`) and this
theorem is unconditional.

**And it is unfoldable.**  `wiiMjL2Equiv` routes through `Exists.choose` at
`leEpsilon_at_edgeSummandG`, which would make `hfix` a statement about an arbitrary chosen map —
unprovable.  It is not: that `Exists` carries `RQ2-2.20-C1`'s **pin**,
`e (a ⊗ₜ v) η = Twist.ofL a ⊗ₜ v`, so `.choose_spec` determines the chosen isomorphism on
generators and the chain computes.  That pin was upgraded from `Nonempty` to `∃ e, pin` for
`RQ2-2.20`; this is its **fifth** consumer, and the first on the `H` side.

@census none (G4 engine for `RQ2-2.28`; clause witnesses `RQ2-2.28-C2`, `RQ2-1.08-C9`) -/
theorem phiEdgeRep_equivariant
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (i j : Γ.VertexOrbit)
    [Fintype (Γ.EdgeOrbit i j)] [DecidableEq (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch i j ε))]
    [∀ ε : Γ.EdgeOrbit i j, DecidableEq (EdgeChoice.CosetIndex Γ (ch i j ε))]
    (ε : Γ.EdgeOrbit i j)
    (k : Gal(L/K)) (hk : k • Γ.edgeRep ε = Γ.edgeRep ε) (x : hObj V WK i) :
    hPhi V WK k j (phiEdgeRep V WK hWK ch i j ε x)
      = phiEdgeRep V WK hWK ch i j ε (hPhi V WK k i x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a w =>
      rw [hPhi_tmul, phiEdgeRep_tmul, phiEdgeRep_tmul, hPhi_smul,
        hPhi_fix_symm V WK _ (phiEdgeAt_fixed V WK hWK ch ε k hk w)]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

/-! ### `e_fix`'s forward map — `W_j → M(v_j)^{G_{v_j}}`  (G4)

`wFixedDescent` (d808c6a) gives `e_fix`'s *content* as Galois descent over `L_j`.  Its **forward
map** has a second, entirely elementary description that is the one the edge datum consumes:
`M(v_j) = L ⊗_K W_{j,K}` contains `L_j ⊗_K W_{j,K} ≅ W_j` (clause `C4`), and everything in that
part is fixed by `G_{v_j} = Gal(L/L_j)` for the reason that `hPhi` is `σ ⊗ 1` and `σ ∈ G_{v_j}`
fixes `L_j` pointwise.  No descent theorem is needed to *land* in the fixed points — only to know
the map is onto them, which is what `wFixedDescent` supplies.

`hPhi_fix_rTensor` is stated for the whole `L_j`-part rather than for `kFormIncl`'s image, because
that is the form the `G_{e}`-fixing argument needs: for an edge `e` at `v_j`, `G_e ≤ G_{v_j}`
(`stabilizer_le_target`), so anything in the `L_j`-part is `G_e`-fixed too.

@census none (G4 engine for `RQ2-2.28`)
-/

/-- **The `L_j`-part of `M(v_j)` is `G_{v_j}`-fixed.**  `hPhi` is `σ ⊗ 1` and `σ ∈ G_{v_j}` fixes
`L_j = L^{G_{v_j}}` pointwise.  @census none (helper) -/
theorem hPhi_fix_rTensor (j : Γ.VertexOrbit)
    (h : Gal(L/K)) (hh : h • Γ.vertexRep j = Γ.vertexRep j)
    (z : (Γ.toSpecies.L j) ⊗[K] ↥(WK j)) :
    hPhi V WK h j (LinearMap.rTensor ↥(WK j)
        ((Algebra.linearMap (Γ.toSpecies.L j) L).restrictScalars K) z)
      = LinearMap.rTensor ↥(WK j)
        ((Algebra.linearMap (Γ.toSpecies.L j) L).restrictScalars K) z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c w =>
      rw [LinearMap.rTensor_tmul]
      show hPhi V WK h j ((algebraMap (Γ.toSpecies.L j) L c) ⊗ₜ[K] w) = _
      rw [hPhi_tmul]
      congr 1
      exact (IntermediateField.mem_fixedField_iff _ _).mp c.2 h hh
  | add p q hp hq => rw [map_add, map_add, hp, hq]

/-- **`e_fix`'s forward map**: `W_j → M(v_j)`, through clause `C4` and the `L_j`-part.
@census none (helper for `RQ2-2.28`) -/
noncomputable def kFormIncl (j : Γ.VertexOrbit) (hj : IsKRationalStructure V j (WK j)) :
    V.W j →ₗ[K] hObj V WK j :=
  (LinearMap.rTensor ↥(WK j)
      ((Algebra.linearMap (Γ.toSpecies.L j) L).restrictScalars K)) ∘ₗ
    ((kRatEquiv V WK hj).symm.toLinearMap.restrictScalars K)

/-- …and it lands in the `G_{v_j}`-fixed points.  @census none (helper) -/
theorem hPhi_fix_kFormIncl (j : Γ.VertexOrbit) (hj : IsKRationalStructure V j (WK j))
    (h : Gal(L/K)) (hh : h • Γ.vertexRep j = Γ.vertexRep j) (y : V.W j) :
    hPhi V WK h j (kFormIncl V WK j hj y) = kFormIncl V WK j hj y :=
  hPhi_fix_rTensor V WK j h hh _


end EdgeDatum

/-! ### `H.obj V` — the eight non-edge fields, and what is left  (G4)

`H.obj V` is an `FDRep Γ` with ten fields.  **Eight of them are already paid for**: the `RQ2-2.27`
engine above built `hPhi` precisely to be the `φ` of this representation, and its four laws
(`hPhi_smul`, `hPhi_comp`, `hPhi_one`, `hPhi_isOpen`) are the `semilinear`, `cocycle` and `smooth`
fields once the orbit indexing is bridged by `hObjCast`.  `finiteDimensional` is a two-step tower:
`W_i` is finite over `L_i` (`Rep.finite_W'`), `L_i` is finite over `K` (étale), so `W_{i,K} ⊆ W_i`
is finite over `K` and `L ⊗_K W_{i,K}` is finite over `L`.

So `hObjRepOf` takes the **edge datum as a parameter** — `φEdge` together with its equivariance —
and supplies everything else.  That is not a stopgap: it is the honest statement of where the
remaining content of `RQ2-2.28` lives.  The eight fields are formal consequences of `RQ2-2.27`; the
edge field is where clause `C2`'s cocycle and clause `C3`'s square do their work, and isolating it
means the edge construction can be built and revised against a **fixed, compiled** carrier instead
of against a moving nine-field target.

Two transport lemmas are the whole bridging cost, and both are `subst`-and-`rfl`:
`hObjCast_smul` (the transport is `L`-linear) and `hPhi_hObjCast_heq` (`hPhi` commutes with it,
heterogeneously — the only form in which that is stateable, and all the `cocycle` field needs).

@census none (G4 engine for `RQ2-2.28`)
-/

section HObjRep
variable (V : EtaleSpecies.Rep Γ.toSpecies)
  (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i))

/-- `hPhi` commutes with the orbit transport, heterogeneously.  @census none (helper) -/
theorem hPhi_hObjCast_heq {i i' : Γ.VertexOrbit} (h : i = i') (σ : Gal(L/K))
    (x : hObj V WK i) :
    HEq (hPhi V WK σ i' (hObjCast V WK h x)) (hPhi V WK σ i x) := by subst h; rfl

/-- The orbit transport is `L`-linear.  @census none (helper) -/
theorem hObjCast_smul {i i' : Γ.VertexOrbit} (h : i = i') (a : L) (x : hObj V WK i) :
    hObjCast V WK h (a • x) = a • hObjCast V WK h x := by subst h; rfl

/-- **`H.obj V`, given its edge datum.**  The eight non-edge fields of the `FDRep` — everything
`RQ2-2.27` already proved — with `φEdge` and clause `RQ2-1.08-C9` taken as parameters.

@census none (helper for `RQ2-2.28`) -/
noncomputable def hObjRepOf
    (φE : ∀ e : Γ.E, hObj V WK (Γ.vertexClass (Γ.toRQuiver.source e))
      →ₗ[L] hObj V WK (Γ.vertexClass (Γ.toRQuiver.target e)))
    (hφE : ∀ (σ : Gal(L/K)) (e : Γ.E)
        (m : hObj V WK (Γ.vertexClass (Γ.toRQuiver.source e)))
        (m' : hObj V WK (Γ.vertexClass (Γ.toRQuiver.source (σ • e)))),
        (⟨Γ.toRQuiver.source (σ • e), m'⟩ :
            Σ v : Γ.V, hObj V WK (Γ.vertexClass v))
            = ⟨σ • Γ.toRQuiver.source e,
                hObjCast V WK (vertexClass_smul σ (Γ.toRQuiver.source e)).symm
                  (hPhi V WK σ (Γ.vertexClass (Γ.toRQuiver.source e)) m)⟩ →
        (⟨Γ.toRQuiver.target (σ • e), φE (σ • e) m'⟩ :
            Σ v : Γ.V, hObj V WK (Γ.vertexClass v))
            = ⟨σ • Γ.toRQuiver.target e,
                hObjCast V WK (vertexClass_smul σ (Γ.toRQuiver.target e)).symm
                  (hPhi V WK σ (Γ.vertexClass (Γ.toRQuiver.target e)) (φE e m))⟩) :
    FDRep Γ where
  M v := hObj V WK (Γ.vertexClass v)
  φ σ v := (hPhi V WK σ (Γ.vertexClass v)).trans
    (hObjCast V WK (vertexClass_smul σ v).symm)
  semilinear σ v a m := by
    show hObjCast V WK _ (hPhi V WK σ _ (a • m)) = _
    rw [hPhi_smul, hObjCast_smul]
    rfl
  cocycle σ τ v m := by
    refine Sigma.ext (mul_smul σ τ v).symm ?_
    refine HEq.trans (hObjCast_heq V WK _ _) ?_
    refine HEq.trans ?_ (hObjCast_heq V WK _ _).symm
    exact (hPhi_hObjCast_heq V WK (vertexClass_smul τ v).symm σ _).trans
      (heq_of_eq (hPhi_comp V WK σ τ (Γ.vertexClass v) m))
  smooth x := hPhi_isOpen V WK x
  φEdge := φE
  edge_equivariance := hφE
  finiteDimensional v := by
    haveI : Module.Finite K (V.W (Γ.vertexClass v)) :=
      Module.Finite.trans (Γ.toSpecies.L (Γ.vertexClass v))ᵐᵒᵖ (V.W (Γ.vertexClass v))
    haveI : Module.Finite K ↥(WK (Γ.vertexClass v)) :=
      Module.Finite.of_injective (WK (Γ.vertexClass v)).subtype Subtype.val_injective
    exact Module.Finite.base_change K L ↥(WK (Γ.vertexClass v))

@[simp] theorem hObjRepOf_M (φE) (hφE) (v : Γ.V) :
    (hObjRepOf V WK φE hφE).toRep.M v = hObj V WK (Γ.vertexClass v) := rfl

@[simp] theorem hObjRepOf_φEdge (φE) (hφE) (e : Γ.E) :
    (hObjRepOf V WK φE hφE).toRep.φEdge e = φE e := rfl

end HObjRep

noncomputable local instance instFintypeEdgeOrbit (i j : Γ.VertexOrbit) :
    Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
noncomputable local instance instDecEqEdgeOrbit (i j : Γ.VertexOrbit) :
    DecidableEq (Γ.EdgeOrbit i j) := Classical.decEq _
noncomputable local instance instFintypeCoset {i j : Γ.VertexOrbit}
    {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε) :
    Fintype (EdgeChoice.CosetIndex Γ ch) := @Fintype.ofFinite _ (finite_cosetIndex ch)
noncomputable local instance instDecEqCoset {i j : Γ.VertexOrbit}
    {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε) :
    DecidableEq (EdgeChoice.CosetIndex Γ ch) := Classical.decEq _

/-! ### `φ_e` for every edge, and `H.obj V`  (G4)

`phiEdgeRep_equivariant` being unconditional, the rest of the edge datum is mechanical — but there
is one design point worth naming, because it is what keeps the whole section free of transports.

**Index the edge by a *fixed* pair of vertex orbits.**  The naive `φ_e := φ_{g_e} ∘ φ_{e_{ε(e)}} ∘
φ_{g_e}^{-1}` reads the orbit off `e` itself, so `e` and `σ · e` land in `EdgeOrbit` at *different*
(propositionally equal) indices, and every step of the equivariance argument has to be transported.
`edgeClassAt i j e hs ht` instead takes the orbits as parameters and the membership as hypotheses,
so `e` and `σ · e` can be read at **one and the same** `(i,j)` — and there
`edgeClassAt i j (σ·e) _ _ = edgeClassAt i j e _ _` is a plain `Quotient.sound`, an equation
between terms of one type.  The entire group-theoretic content then happens at fixed indices
(`phiEdgeConj_equivariant`), and the only transport in the section is `phiEdgeAtIdx_congr`, whose
proof is `subst; subst; rfl` — proof irrelevance doing all the work.

The group bookkeeping is three lines: with `g · e_ε = e` and `g' · e_ε = σ·e`, the element
`k := g'^{-1} σ g` fixes `e_ε`, and `phiEdgeRep_equivariant` at `k` is the whole of clause
`RQ2-1.08-C9`.

`hObjRep` is then `hObjRepOf` fed its edge datum: **`H.obj V`, all ten fields**.

**Instances.**  The `Fintype`/`DecidableEq` on `EdgeOrbit` and `CosetIndex` are `local instance`s
here rather than `letI`s at each use, so that every occurrence is the *same term* — `CONVENTIONS.md`
§3's decidability entry, avoided by construction rather than diagnosed later.

@census none (G4 engine for `RQ2-2.28`)
-/

section EdgeField


variable (V : EtaleSpecies.Rep Γ.toSpecies)
  (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i))

/-- `hPhi`'s inverse is `hPhi` at the inverse. -/
theorem hPhi_symm_eq (g : Gal(L/K)) (i : Γ.VertexOrbit) (x : hObj V WK i) :
    (hPhi V WK g i).symm x = hPhi V WK g⁻¹ i x := by
  refine (hPhi V WK g i).injective ?_
  rw [AddEquiv.apply_symm_apply, hPhi_comp, mul_inv_cancel, hPhi_one]

/-- The orbit of an edge, at a **fixed** pair of vertex orbits — which is what keeps the
equivariance statement transport-free. -/
def edgeClassAt (i j : Γ.VertexOrbit) (e : Γ.E)
    (hs : Γ.vertexClass (Γ.toRQuiver.source e) = i)
    (ht : Γ.vertexClass (Γ.toRQuiver.target e) = j) : Γ.EdgeOrbit i j :=
  ⟦⟨e, hs, ht⟩⟧

theorem edgeClassAt_smul {i j : Γ.VertexOrbit} (σ : Gal(L/K)) (e : Γ.E)
    (hs : Γ.vertexClass (Γ.toRQuiver.source e) = i)
    (ht : Γ.vertexClass (Γ.toRQuiver.target e) = j)
    (hs' : Γ.vertexClass (Γ.toRQuiver.source (σ • e)) = i)
    (ht' : Γ.vertexClass (Γ.toRQuiver.target (σ • e)) = j) :
    edgeClassAt i j (σ • e) hs' ht' = edgeClassAt i j e hs ht :=
  Quotient.sound ⟨σ, Subtype.ext rfl⟩

theorem exists_smul_edgeRep_at (i j : Γ.VertexOrbit) (e : Γ.E)
    (hs : Γ.vertexClass (Γ.toRQuiver.source e) = i)
    (ht : Γ.vertexClass (Γ.toRQuiver.target e) = j) :
    ∃ g : Gal(L/K), g • Γ.edgeRep (edgeClassAt i j e hs ht) = e := by
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel Gal(L/K) (Γ.edgeSet i j)) (⟨e, hs, ht⟩)
  refine ⟨g⁻¹, ?_⟩
  show g⁻¹ • ((⟦(⟨e, hs, ht⟩ : Γ.edgeSet i j)⟧.out : Γ.edgeSet i j) : Γ.E) = e
  rw [← congrArg Subtype.val hg]
  show g⁻¹ • (g • e) = e
  rw [inv_smul_smul]

/-- The translation carrying the orbit representative to `e`. -/
noncomputable def edgeTrans (i j : Γ.VertexOrbit) (e : Γ.E)
    (hs : Γ.vertexClass (Γ.toRQuiver.source e) = i)
    (ht : Γ.vertexClass (Γ.toRQuiver.target e) = j) : Gal(L/K) :=
  (exists_smul_edgeRep_at i j e hs ht).choose

theorem edgeTrans_spec (i j : Γ.VertexOrbit) (e : Γ.E)
    (hs : Γ.vertexClass (Γ.toRQuiver.source e) = i)
    (ht : Γ.vertexClass (Γ.toRQuiver.target e) = j) :
    edgeTrans i j e hs ht • Γ.edgeRep (edgeClassAt i j e hs ht) = e :=
  (exists_smul_edgeRep_at i j e hs ht).choose_spec

variable (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
  (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)

/-- `φ_{e_ε}` conjugated by a translation `g` — `φ_e` for the edge `g · e_ε`. -/
noncomputable def phiEdgeConj (i j : Γ.VertexOrbit) (ε : Γ.EdgeOrbit i j) (g : Gal(L/K)) :
    hObj V WK i →ₗ[L] hObj V WK j where
  toFun x := hPhi V WK g j (phiEdgeRep V WK hWK ch i j ε (hPhi V WK g⁻¹ i x))
  map_add' x y := by rw [map_add, map_add, map_add]
  map_smul' c x := by
    show hPhi V WK g j (phiEdgeRep V WK hWK ch i j ε (hPhi V WK g⁻¹ i (c • x))) = _
    rw [hPhi_smul, LinearMap.map_smul, hPhi_smul]
    show (g (g⁻¹ c)) • _ = _
    rw [show g (g⁻¹ c) = c from by
      have := hPhi_comp V WK g g⁻¹ i (0 : hObj V WK i)
      exact congrArg (fun (t : Gal(L/K)) => t c) (mul_inv_cancel g) ]
    rfl

theorem phiEdgeConj_apply (i j : Γ.VertexOrbit) (ε : Γ.EdgeOrbit i j) (g : Gal(L/K))
    (x : hObj V WK i) :
    phiEdgeConj V WK hWK ch i j ε g x
      = hPhi V WK g j (phiEdgeRep V WK hWK ch i j ε (hPhi V WK g⁻¹ i x)) := rfl

/-- **Clause `RQ2-1.08-C9` for the edge datum**, in transport-free form. -/
theorem phiEdgeConj_equivariant (i j : Γ.VertexOrbit) (ε : Γ.EdgeOrbit i j)
    (g g' σ : Gal(L/K)) (hk : (g'⁻¹ * σ * g) • Γ.edgeRep ε = Γ.edgeRep ε)
    (x : hObj V WK i) :
    phiEdgeConj V WK hWK ch i j ε g' (hPhi V WK σ i x)
      = hPhi V WK σ j (phiEdgeConj V WK hWK ch i j ε g x) := by
  rw [phiEdgeConj_apply, phiEdgeConj_apply, hPhi_comp]
  rw [show g'⁻¹ * σ = (g'⁻¹ * σ * g) * g⁻¹ from by group, ← hPhi_comp,
    ← phiEdgeRep_equivariant V WK hWK ch i j ε _ hk, hPhi_comp, hPhi_comp]
  congr 2
  group

/-- `φ_e` at a **fixed** pair of vertex orbits. -/
noncomputable def phiEdgeAtIdx (i j : Γ.VertexOrbit) (e : Γ.E)
    (hs : Γ.vertexClass (Γ.toRQuiver.source e) = i)
    (ht : Γ.vertexClass (Γ.toRQuiver.target e) = j) :
    hObj V WK i →ₗ[L] hObj V WK j :=
  phiEdgeConj V WK hWK ch i j (edgeClassAt i j e hs ht) (edgeTrans i j e hs ht)

/-- The index transport: `subst` and proof irrelevance, nothing more. -/
theorem phiEdgeAtIdx_congr {i i' j j' : Γ.VertexOrbit} (hii : i = i') (hjj : j = j')
    (e : Γ.E) (hs : Γ.vertexClass (Γ.toRQuiver.source e) = i)
    (ht : Γ.vertexClass (Γ.toRQuiver.target e) = j)
    (hs' : Γ.vertexClass (Γ.toRQuiver.source e) = i')
    (ht' : Γ.vertexClass (Γ.toRQuiver.target e) = j') (x : hObj V WK i) :
    hObjCast V WK hjj (phiEdgeAtIdx V WK hWK ch i j e hs ht x)
      = phiEdgeAtIdx V WK hWK ch i' j' e hs' ht' (hObjCast V WK hii x) := by
  subst hii; subst hjj; rfl

/-- **The edge datum of `H.obj V`**: `φ_e` for every edge. -/
noncomputable def phiEdgeFull (e : Γ.E) :
    hObj V WK (Γ.vertexClass (Γ.toRQuiver.source e))
      →ₗ[L] hObj V WK (Γ.vertexClass (Γ.toRQuiver.target e)) :=
  phiEdgeAtIdx V WK hWK ch _ _ e rfl rfl

/-- `phiEdgeFull` unfolded — a `rfl` pin, so consumers rewrite rather than unify.
@census none (helper) -/
theorem phiEdgeFull_eq (e : Γ.E) :
    phiEdgeFull V WK hWK ch e
      = phiEdgeAtIdx V WK hWK ch (Γ.vertexClass (Γ.toRQuiver.source e))
          (Γ.vertexClass (Γ.toRQuiver.target e)) e rfl rfl := rfl

/-- **Clause `RQ2-1.08-C9` for `H.obj V`** — the `edge_equivariance` field. -/
theorem phiEdgeFull_edge_equivariance (σ : Gal(L/K)) (e : Γ.E)
    (m : hObj V WK (Γ.vertexClass (Γ.toRQuiver.source e)))
    (m' : hObj V WK (Γ.vertexClass (Γ.toRQuiver.source (σ • e))))
    (hm : (⟨Γ.toRQuiver.source (σ • e), m'⟩ : Σ v : Γ.V, hObj V WK (Γ.vertexClass v))
        = ⟨σ • Γ.toRQuiver.source e,
            hObjCast V WK (vertexClass_smul σ (Γ.toRQuiver.source e)).symm
              (hPhi V WK σ (Γ.vertexClass (Γ.toRQuiver.source e)) m)⟩) :
    (⟨Γ.toRQuiver.target (σ • e), phiEdgeFull V WK hWK ch (σ • e) m'⟩
        : Σ v : Γ.V, hObj V WK (Γ.vertexClass v))
      = ⟨σ • Γ.toRQuiver.target e,
          hObjCast V WK (vertexClass_smul σ (Γ.toRQuiver.target e)).symm
            (hPhi V WK σ (Γ.vertexClass (Γ.toRQuiver.target e))
              (phiEdgeFull V WK hWK ch e m))⟩ := by
  have hsi : Γ.vertexClass (Γ.toRQuiver.source (σ • e))
      = Γ.vertexClass (Γ.toRQuiver.source e) := by
    rw [Γ.source_smul]; exact vertexClass_smul σ _
  have htj : Γ.vertexClass (Γ.toRQuiver.target (σ • e))
      = Γ.vertexClass (Γ.toRQuiver.target e) := by
    rw [Γ.target_smul]; exact vertexClass_smul σ _
  rw [Sigma.mk.injEq] at hm
  have hm2 : hObjCast V WK hsi m'
      = hPhi V WK σ (Γ.vertexClass (Γ.toRQuiver.source e)) m :=
    eq_of_heq ((hObjCast_heq V WK hsi m').trans
      (hm.2.trans (hObjCast_heq V WK _ _)))
  refine Sigma.ext (Γ.target_smul σ e) ?_
  refine HEq.trans ?_ (hObjCast_heq V WK _ _).symm
  refine HEq.trans (hObjCast_heq V WK htj _).symm (heq_of_eq ?_)
  -- now an honest equality in `hObj V WK j`
  rw [phiEdgeFull, phiEdgeAtIdx_congr V WK hWK ch hsi htj (σ • e) rfl rfl hsi htj m', hm2]
  have hcls : edgeClassAt (Γ.vertexClass (Γ.toRQuiver.source e))
        (Γ.vertexClass (Γ.toRQuiver.target e)) (σ • e) hsi htj
      = edgeClassAt (Γ.vertexClass (Γ.toRQuiver.source e))
        (Γ.vertexClass (Γ.toRQuiver.target e)) e rfl rfl :=
    edgeClassAt_smul σ e rfl rfl hsi htj
  have hg := edgeTrans_spec (Γ.vertexClass (Γ.toRQuiver.source e))
    (Γ.vertexClass (Γ.toRQuiver.target e)) e rfl rfl
  have hg' := edgeTrans_spec (Γ.vertexClass (Γ.toRQuiver.source e))
    (Γ.vertexClass (Γ.toRQuiver.target e)) (σ • e) hsi htj
  rw [hcls] at hg'
  have hk : ((edgeTrans (Γ.vertexClass (Γ.toRQuiver.source e))
        (Γ.vertexClass (Γ.toRQuiver.target e)) (σ • e) hsi htj)⁻¹ * σ *
      (edgeTrans (Γ.vertexClass (Γ.toRQuiver.source e))
        (Γ.vertexClass (Γ.toRQuiver.target e)) e rfl rfl)) •
        Γ.edgeRep (edgeClassAt (Γ.vertexClass (Γ.toRQuiver.source e))
          (Γ.vertexClass (Γ.toRQuiver.target e)) e rfl rfl)
      = Γ.edgeRep (edgeClassAt (Γ.vertexClass (Γ.toRQuiver.source e))
          (Γ.vertexClass (Γ.toRQuiver.target e)) e rfl rfl) := by
    rw [mul_smul, mul_smul, hg, inv_smul_eq_iff]
    exact hg'.symm
  show phiEdgeConj V WK hWK ch _ _ (edgeClassAt _ _ (σ • e) hsi htj) _ _ = _
  rw [hcls]
  exact phiEdgeConj_equivariant V WK hWK ch _ _ _ _ _ σ hk m

/-- **`H.obj V`** — all ten `FDRep` fields. -/
noncomputable def hObjRep : FDRep Γ :=
  hObjRepOf V WK (phiEdgeFull V WK hWK ch)
    (fun σ e m m' hm => phiEdgeFull_edge_equivariance V WK hWK ch σ e m m' hm)

@[simp] theorem hObjRep_M (v : Γ.V) :
    (hObjRep V WK hWK ch).toRep.M v = hObj V WK (Γ.vertexClass v) := rfl

@[simp] theorem hObjRep_phiEdge (e : Γ.E) :
    (hObjRep V WK hWK ch).toRep.φEdge e = phiEdgeFull V WK hWK ch e := rfl

end EdgeField

/-! ### `e_fix`'s two descriptions agree, and `H.obj V`'s `φ'` is `hPhi`  (G4)

Three small facts that `e_fix`'s assembly consumes, and that are worth having named regardless.

* `hObjRep_phi'_apply` — `H.obj V`'s transported `φ'` at a **fixed** vertex is `hPhi` on the nose.
  Both transports (`Rep.eqCast` along `σ v = v`, `hObjCast` along `Gv = G(σv)`) are heterogeneously
  the identity, so their composite is; `eq_of_heq` of the two `HEq`s is the whole proof.  This is
  what turns `Rep.vertexFixed`'s membership condition into a statement about `hPhi`.

* `kFormIncl_eq` — the two descriptions of `e_fix`'s forward map are the same map:
  `W_j ⊆ L_j ⊗_K W_{j,K} ⊆ L ⊗_K W_{j,K}` (§62.6, elementary) and `w ↦ 1 ⊗ₜ w` read through
  `hObjEquivBaseChange` (§d808c6a, the base-change form Galois descent consumes).  They were built
  from opposite ends — one to make `hfix` trivial, one to make descent applicable — and the
  identification is what lets the *elementary* description carry the map and the *descent*
  description carry its surjectivity.

@census none (G4 engine for `RQ2-2.28`)
-/

section EFix
variable (V : EtaleSpecies.Rep Γ.toSpecies)
  (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i))
  (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
  (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)

omit [IsGalois K L] in
theorem eqCast_heq (M : Rep Γ) {v w : Γ.V} (h : v = w) (m : M.M v) :
    HEq (M.eqCast h m) m := by subst h; rfl

/-- `H.obj V`'s `φ'` at a fixed vertex is just `hPhi`. -/
theorem hObjRep_phi'_apply (σ : Gal(L/K)) (v : Γ.V) (h : σ • v = v)
    (m : (hObjRep V WK hWK ch).toRep.M v) :
    (hObjRep V WK hWK ch).toRep.φ' σ h m = hPhi V WK σ (Γ.vertexClass v) m := by
  rw [Rep.φ'_apply]
  refine eq_of_heq (((eqCast_heq _ h _)).trans ?_)
  exact hObjCast_heq V WK (vertexClass_smul σ v).symm _

/-- `kFormIncl` **is** `w ↦ 1 ⊗ₜ w` read through `C4` — the two descriptions of `e_fix`'s forward
map agree. -/
theorem kFormIncl_eq (i : Γ.VertexOrbit) (hi : IsKRationalStructure V i (WK i))
    (w : V.W i) :
    kFormIncl V WK i hi w
      = hObjEquivBaseChange V WK i hi ((1 : L) ⊗ₜ[Γ.toSpecies.L i] w) := by
  have key : ∀ t : (Γ.toSpecies.L i) ⊗[K] ↥(WK i),
      LinearMap.rTensor ↥(WK i)
          ((Algebra.linearMap (Γ.toSpecies.L i) L).restrictScalars K) t
        = hObjEquivBaseChange V WK i hi
            ((1 : L) ⊗ₜ[Γ.toSpecies.L i] (kRatEquiv V WK hi t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, TensorProduct.tmul_zero, map_zero]
    | tmul c w0 =>
        rw [LinearMap.rTensor_tmul, hObjEquivBaseChange_tmul, one_mul]
        rfl
    | add p q hp hq =>
        rw [map_add, map_add, TensorProduct.tmul_add, map_add, hp, hq]
  have := key ((kRatEquiv V WK hi).symm w)
  rwa [LinearEquiv.apply_symm_apply] at this


/-! #### `e_fix` assembled  (G4)

The map is `kFormIncl` — clause `C4`, nothing else — transported to the vertex `v_i` by
`hObjCast` and landing in the fixed points by `hPhi_fix_kFormIncl`.  **It is a definition, not a
choice**, which is the constraint `§61`'s probe identified and the coordinator made binding.

Bijectivity is then established *about that fixed map*, never by selecting one:

* **injective** — `kFormIncl` is `kRatEquiv.symm` followed by `rTensor` of the injection
  `L_i ↪ L`, and `W_{i,K}` is flat over the field `K`;
* **surjective** — by a rank count.  `vertexDescentEquiv` (`RQ2-2.21`, the `F` side) identifies
  `L ⊗_{L_i} M(v_i)^{G_{v_i}}` with `M(v_i)`, and `hObjEquivBaseChange` identifies
  `L ⊗_{L_i} W_i` with the same space; `Module.rank_baseChange` then gives the two `L_i`-ranks
  equal, and an injective endomorphism-shaped map between finite-dimensional spaces of equal
  dimension is surjective.

**That is the `F` side's descent paying for the `H` side's.** The alternative was to match `hPhi`
against `Descent.galoisTensorAction` along `galStabFieldEquiv` by hand — the "fiddly half" this
row was expected to cost.  `RQ2-2.21` already did that matching, so the `H` side only has to count.

The last step converts `≃ₗ[L_i]` to the row's `≃ₗ[L_iᵐᵒᵖ]`: both actions are the same action read
through `RingEquiv.toOpposite`, so the conversion is `AddEquiv.toLinearEquiv` and one `unop`.
-/

/-- `hObjCast` commutes with `hPhi`, homogeneously. -/
theorem hPhi_hObjCast {i i' : Γ.VertexOrbit} (h : i = i') (σ : Gal(L/K)) (x : hObj V WK i) :
    hPhi V WK σ i' (hObjCast V WK h x) = hObjCast V WK h (hPhi V WK σ i x) := by
  subst h; rfl

/-- The orbit transport, `L`-linearly. -/
noncomputable def hObjCastL {i i' : Γ.VertexOrbit} (h : i = i') :
    hObj V WK i ≃ₗ[L] hObj V WK i' := by subst h; exact LinearEquiv.refl _ _

/-- `kFormIncl` is `L_i`-linear. -/
theorem kFormIncl_smul (i : Γ.VertexOrbit) (c : Γ.toSpecies.L i) (w : V.W i) :
    kFormIncl V WK i (hWK i) (c • w)
      = (algebraMap (Γ.toSpecies.L i) L c) • kFormIncl V WK i (hWK i) w := by
  rw [kFormIncl_eq, kFormIncl_eq, ← LinearEquiv.map_smul]
  congr 1
  rw [TensorProduct.tmul_smul]
  exact (algebraMap_smul L c _).symm

/-- **`e_fix`'s forward map**, into the fixed points. -/
noncomputable def eFixFwd (i : Γ.VertexOrbit) :
    V.W i →ₗ[Γ.toSpecies.L i]
      ↥((hObjRep V WK hWK ch).toRep.vertexFixed (Γ.vertexRep i)) where
  toFun w := ⟨hObjCast V WK (Γ.vertexClass_vertexRep i).symm
      (kFormIncl V WK i (hWK i) w), by
    intro σ
    rw [hObjRep_phi'_apply, hPhi_hObjCast]
    congr 1
    exact hPhi_fix_kFormIncl V WK i (hWK i) (σ : Gal(L/K)) σ.2 w⟩
  map_add' w w' := by
    refine Subtype.ext ?_
    show hObjCast V WK _ (kFormIncl V WK i (hWK i) (w + w')) = _
    rw [map_add, map_add]; rfl
  map_smul' c w := by
    refine Subtype.ext ?_
    show hObjCast V WK _ (kFormIncl V WK i (hWK i) (c • w)) = _
    rw [kFormIncl_smul]
    show hObjCast V WK _ ((algebraMap (Γ.toSpecies.L i) L c) • _) = _
    rw [hObjCast_smul]
    rfl

/-- `W_i` is finite over `L_i` (un-opposed): the two actions have the same spans. -/
theorem finite_L_W (i : Γ.VertexOrbit) : Module.Finite (Γ.toSpecies.L i) (V.W i) := by
  obtain ⟨S, hS⟩ := Module.finite_def.mp (EtaleSpecies.Rep.finite_W' Γ.toSpecies V i)
  refine Module.finite_def.mpr ⟨S, ?_⟩
  refine eq_top_iff.mpr fun x hxt => ?_
  clear hxt
  have hx : x ∈ Submodule.span (Γ.toSpecies.L i)ᵐᵒᵖ (S : Set (V.W i)) := by
    rw [hS]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha =>
      have hc : (c • a : V.W i) = (MulOpposite.unop c) • a := rfl
      rw [hc]
      exact Submodule.smul_mem _ _ ha

theorem eFixFwd_injective (i : Γ.VertexOrbit) :
    Function.Injective (eFixFwd V WK hWK ch i) := by
  intro w w' h
  have h1 : kFormIncl V WK i (hWK i) w = kFormIncl V WK i (hWK i) w' := by
    have := congrArg Subtype.val h
    exact (hObjCast V WK (Γ.vertexClass_vertexRep i).symm).injective this
  have h2 : Function.Injective (kFormIncl V WK i (hWK i)) := by
    intro a b hab
    refine (kRatEquiv V WK (hWK i)).symm.injective ?_
    exact Module.Flat.rTensor_preserves_injective_linearMap
      ((Algebra.linearMap (Γ.toSpecies.L i) L).restrictScalars K)
      (fun p q hpq => (algebraMap (Γ.toSpecies.L i) L).injective hpq) hab
  exact h2 h1

theorem eFixFwd_rank (i : Γ.VertexOrbit) :
    Module.rank (Γ.toSpecies.L i) (V.W i)
      = Module.rank (Γ.toSpecies.L i)
          ↥((hObjRep V WK hWK ch).toRep.vertexFixed (Γ.vertexRep i)) := by
  have hF : Module.rank L (L ⊗[Γ.toSpecies.L i]
        ↥((hObjRep V WK hWK ch).toRep.vertexFixed (Γ.vertexRep i)))
      = Module.rank L ((hObjRep V WK hWK ch).toRep.M (Γ.vertexRep i)) :=
    (vertexDescentEquiv (hObjRep V WK hWK ch).toRep (Γ.vertexRep i)).rank_eq
  have hW : Module.rank L (L ⊗[Γ.toSpecies.L i] (V.W i))
      = Module.rank L (hObj V WK i) :=
    (hObjEquivBaseChange V WK i (hWK i)).rank_eq
  have hM : Module.rank L ((hObjRep V WK hWK ch).toRep.M (Γ.vertexRep i))
      = Module.rank L (hObj V WK i) :=
    (hObjCastL V WK (Γ.vertexClass_vertexRep i)).rank_eq
  rw [Module.rank_baseChange] at hF hW
  have := hW.trans (hM.symm.trans hF.symm)
  exact Cardinal.lift_injective this

theorem eFixFwd_bijective (i : Γ.VertexOrbit) :
    Function.Bijective (eFixFwd V WK hWK ch i) := by
  haveI : Module.Finite (Γ.toSpecies.L i) (V.W i) := finite_L_W V i
  haveI : Module.Finite (Γ.toSpecies.L i)
      ↥((hObjRep V WK hWK ch).toRep.vertexFixed (Γ.vertexRep i)) :=
    Rep.finite_vertexFixed (hObjRep V WK hWK ch).toRep (Γ.vertexRep i)
  have hfr : Module.finrank (Γ.toSpecies.L i) (V.W i)
      = Module.finrank (Γ.toSpecies.L i)
          ↥((hObjRep V WK hWK ch).toRep.vertexFixed (Γ.vertexRep i)) :=
    congrArg Cardinal.toNat (eFixFwd_rank V WK hWK ch i)
  exact ⟨eFixFwd_injective V WK hWK ch i,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp
      (eFixFwd_injective V WK hWK ch i)⟩

/-- **`e_fix`** — `M(v_i)^{G_{v_i}} ≅ W_i`. -/
noncomputable def eFix (i : Γ.VertexOrbit) :
    ↥((hObjRep V WK hWK ch).toRep.vertexFixed (Γ.vertexRep i))
      ≃ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] V.W i :=
  AddEquiv.toLinearEquiv
    (LinearEquiv.ofBijective (eFixFwd V WK hWK ch i)
      (eFixFwd_bijective V WK hWK ch i)).symm.toAddEquiv
    (fun c x => by
      exact (LinearEquiv.ofBijective (eFixFwd V WK hWK ch i)
        (eFixFwd_bijective V WK hWK ch i)).symm.map_smul (MulOpposite.unop c) x)

/-! #### `RQ2-2.28-H2`(a) step 2 — reading `phiComp` for `H.obj V`  (G4)

Every map in `phiComp` is a transported one (`φ'`, `φEdge'`), and every transport in `H.obj V` is
heterogeneously the identity — `Rep.eqCast` along a vertex equality, `hObjCast` along the induced
orbit equality.  So each factor can be *read* at a chosen orbit, and the reading is `hPhi` for the
`φ'`s and `phiEdgeAtIdx` for the `φEdge'`.  Three `HEq` chains, no computation.

`phiEdgeAtIdx_edgeRep` then says the reading at the orbit **representative** is `phiEdgeRep`
itself: `edgeTrans` at `e_ε` is some element of `G_{e_ε}` (not necessarily `1`, since it is an
`Exists.choose`), and `phiEdgeRep_equivariant` makes conjugation by it the identity.  **That is the
`Exists.choose` in `edgeTrans` washing out**, exactly where it had to.
-/

/-- Reading `H.obj V`'s `φ'` at a chosen orbit.  @census none (helper) -/
theorem hObjRep_phi'_read (σ : Gal(L/K)) {v w : Γ.V} (h : σ • v = w)
    {k : Γ.VertexOrbit} (hv : Γ.vertexClass v = k) (hw : Γ.vertexClass w = k)
    (x : (hObjRep V WK hWK ch).toRep.M v) :
    hObjCast V WK hw ((hObjRep V WK hWK ch).toRep.φ' σ h x)
      = hPhi V WK σ k (hObjCast V WK hv x) := by
  refine eq_of_heq (HEq.trans (hObjCast_heq V WK hw _) ?_)
  rw [Rep.φ'_apply]
  refine HEq.trans (eqCast_heq _ h _) ?_
  refine HEq.trans (hObjCast_heq V WK (vertexClass_smul σ v).symm _) ?_
  exact (hPhi_hObjCast_heq V WK hv σ x).symm

/-- Reading `H.obj V`'s `φEdge'` at chosen orbits.  @census none (helper) -/
theorem hObjRep_phiEdge'_read (e : Γ.E) {a b : Γ.V}
    (ha : Γ.toRQuiver.source e = a) (hb : Γ.toRQuiver.target e = b)
    {k l : Γ.VertexOrbit} (hak : Γ.vertexClass a = k) (hbl : Γ.vertexClass b = l)
    (hs : Γ.vertexClass (Γ.toRQuiver.source e) = k)
    (ht : Γ.vertexClass (Γ.toRQuiver.target e) = l)
    (x : (hObjRep V WK hWK ch).toRep.M a) :
    hObjCast V WK hbl ((hObjRep V WK hWK ch).toRep.φEdge' e ha hb x)
      = phiEdgeAtIdx V WK hWK ch k l e hs ht (hObjCast V WK hak x) := by
  subst ha; subst hb
  show hObjCast V WK hbl ((hObjRep V WK hWK ch).toRep.φEdge e x) = _
  rw [hObjRep_phiEdge]
  show hObjCast V WK hbl (phiEdgeAtIdx V WK hWK ch _ _ e rfl rfl x) = _
  rw [phiEdgeAtIdx_congr V WK hWK ch hs ht e rfl rfl hs ht x]

/-- At the orbit representative, `φ_e` **is** `phiEdgeRep`: `edgeTrans` lands in `G_{e_ε}`, where
the equivariance makes conjugation by it trivial.  @census none (helper) -/
theorem phiEdgeAtIdx_edgeRep (i j : Γ.VertexOrbit) (ε : Γ.EdgeOrbit i j) :
    phiEdgeAtIdx V WK hWK ch i j (Γ.edgeRep ε)
        (Γ.vertexClass_source_edgeRep ε) (Γ.vertexClass_target_edgeRep ε)
      = phiEdgeRep V WK hWK ch i j ε := by
  have hcls : edgeClassAt i j (Γ.edgeRep ε)
      (Γ.vertexClass_source_edgeRep ε) (Γ.vertexClass_target_edgeRep ε) = ε := by
    show ⟦(⟨Γ.edgeRep ε, Γ.vertexClass_source_edgeRep ε,
      Γ.vertexClass_target_edgeRep ε⟩ : Γ.edgeSet i j)⟧ = ε
    rw [show (⟨Γ.edgeRep ε, Γ.vertexClass_source_edgeRep ε,
        Γ.vertexClass_target_edgeRep ε⟩ : Γ.edgeSet i j) = Quotient.out ε from Subtype.ext rfl]
    exact Quotient.out_eq ε
  have hg := edgeTrans_spec i j (Γ.edgeRep ε)
    (Γ.vertexClass_source_edgeRep ε) (Γ.vertexClass_target_edgeRep ε)
  rw [hcls] at hg
  have hginv : (edgeTrans i j (Γ.edgeRep ε)
      (Γ.vertexClass_source_edgeRep ε) (Γ.vertexClass_target_edgeRep ε))⁻¹
      • Γ.edgeRep ε = Γ.edgeRep ε := by rw [inv_smul_eq_iff, hg]
  refine LinearMap.ext fun x => ?_
  show phiEdgeConj V WK hWK ch i j (edgeClassAt i j (Γ.edgeRep ε) _ _) _ x = _
  rw [hcls, phiEdgeConj_apply,
    ← phiEdgeRep_equivariant V WK hWK ch i j ε _ hginv, hPhi_comp, mul_inv_cancel, hPhi_one]


/-- **Step 2 of `H2`(a)**: `Φ_{ij}`'s `(ε,η)`-component for `H.obj V`, read at the orbits.
Three applications of the reading lemmas and one `phiEdgeAtIdx_edgeRep`.  @census none (helper) -/
theorem phiComp_hObjRep_read (i j : Γ.VertexOrbit) (ε : Γ.EdgeOrbit i j)
    (η : EdgeChoice.CosetIndex Γ (ch i j ε))
    (w : ↥((hObjRep V WK hWK ch).toRep.vertexFixed (Γ.vertexRep i))) :
    hObjCast V WK (Γ.vertexClass_vertexRep j)
        ((phiComp (hObjRep V WK hWK ch).toRep (ch i j ε) η w
          : (hObjRep V WK hWK ch).toRep.M (Γ.vertexRep j)))
      = hPhi V WK (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹) j
          (phiEdgeRep V WK hWK ch i j ε
            (hPhi V WK (ch i j ε).σ i
              (hObjCast V WK (Γ.vertexClass_vertexRep i)
                ((w : (hObjRep V WK hWK ch).toRep.M (Γ.vertexRep i)))))) := by
  show hObjCast V WK (Γ.vertexClass_vertexRep j)
      ((hObjRep V WK hWK ch).toRep.φ' _ ((ch i j ε).cosetTarget η)
        ((hObjRep V WK hWK ch).toRep.φEdge' (Γ.edgeRep ε) rfl rfl
          ((hObjRep V WK hWK ch).toRep.φ' (ch i j ε).σ (ch i j ε).sourceVertex
            ((w : (hObjRep V WK hWK ch).toRep.M (Γ.vertexRep i)))))) = _
  rw [hObjRep_phi'_read V WK hWK ch _ ((ch i j ε).cosetTarget η)
      (Γ.vertexClass_target_edgeRep ε) (Γ.vertexClass_vertexRep j),
    hObjRep_phiEdge'_read V WK hWK ch (Γ.edgeRep ε) rfl rfl
      (Γ.vertexClass_source_edgeRep ε) (Γ.vertexClass_target_edgeRep ε)
      (Γ.vertexClass_source_edgeRep ε) (Γ.vertexClass_target_edgeRep ε),
    hObjRep_phi'_read V WK hWK ch _ (ch i j ε).sourceVertex
      (Γ.vertexClass_vertexRep i) (Γ.vertexClass_source_edgeRep ε),
    phiEdgeAtIdx_edgeRep]

/-- **Step 3a**: `phiEdgeAt` moves along the coset index by the `G_{v_j}`-action.  Same three
ingredients as `phiEdgeAt_fixed` — `A_h`, the `balAct` intertwining, and the summand's
components — with the base coset no longer required to be fixed.  @census none (helper) -/
theorem phiEdgeAt_smul_index {i j : Γ.VertexOrbit}
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch i j ε))
    (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) (x : hObj V WK i) :
    phiEdgeAt V WK hWK ch i j ε (σ • η) (hPhi V WK (σ : Gal(L/K)) i x)
      = hPhi V WK (σ : Gal(L/K)) j (phiEdgeAt V WK hWK ch i j ε η x) := by
  set Y := DirectSum.lof L (Γ.EdgeOrbit i j)
      (fun ε => DirectSum (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj V WK i)) ε
      (DirectSum.lof L (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj V WK i) η x)
    with hYdef
  set z := (wiiMjL2Equiv V i j WK hWK ch).symm Y with hzdef
  have hz : wiiMjL2Equiv V i j WK hWK ch z = Y := LinearEquiv.apply_symm_apply _ _
  -- the image of `balAct` is the `(ε, σ·η)`-summand carrying `hPhi σ x`
  have hbal : wiiMjL2Equiv V i j WK hWK ch
      (balAct j (fun _ _ => rfl) (σ : Gal(L/K)) σ.2 z)
      = DirectSum.lof L (Γ.EdgeOrbit i j)
          (fun ε => DirectSum (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj V WK i)) ε
          (DirectSum.lof L (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj V WK i)
            (σ • η) (hPhi V WK (σ : Gal(L/K)) i x)) := by
    refine DFinsupp.ext fun ε' => ?_
    refine DFinsupp.ext fun η' => ?_
    have hA := wiiMjL2Equiv_balAct V WK hWK ch (σ : Gal(L/K)) σ.2 ε' (σ⁻¹ • η') z
    rw [show (⟨(σ : Gal(L/K)), σ.2⟩ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) = σ from rfl,
      smul_inv_smul, hz] at hA
    rw [hA]
    rcases eq_or_ne ε' ε with rfl | hε
    · have h1 : Y ε' = DirectSum.lof L (EdgeChoice.CosetIndex Γ (ch i j ε'))
          (fun _ => hObj V WK i) η x := by
        rw [hYdef, DirectSum.lof_eq_of, DirectSum.of_eq_same]
      have h1' : (DirectSum.lof L (Γ.EdgeOrbit i j)
            (fun ε => DirectSum (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj V WK i)) ε'
            (DirectSum.lof L (EdgeChoice.CosetIndex Γ (ch i j ε')) (fun _ => hObj V WK i)
              (σ • η) (hPhi V WK (σ : Gal(L/K)) i x))) ε'
          = DirectSum.lof L (EdgeChoice.CosetIndex Γ (ch i j ε')) (fun _ => hObj V WK i)
              (σ • η) (hPhi V WK (σ : Gal(L/K)) i x) := by
        rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]
      rw [h1, h1']
      rcases eq_or_ne η' (σ • η) with rfl | hη
      · rw [inv_smul_smul, DirectSum.lof_eq_of, DirectSum.of_eq_same,
          DirectSum.lof_eq_of, DirectSum.of_eq_same]
      · have h3 : σ⁻¹ • η' ≠ η := by
          intro hc; exact hη (by rw [← hc, smul_inv_smul])
        rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ h3,
          DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hη, map_zero]
    · have h4 : Y ε' = 0 := by
        rw [hYdef, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hε]
      have h4' : (DirectSum.lof L (Γ.EdgeOrbit i j)
            (fun ε => DirectSum (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj V WK i)) ε
            (DirectSum.lof L (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj V WK i)
              (σ • η) (hPhi V WK (σ : Gal(L/K)) i x))) ε' = 0 := by
        rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hε]
      rw [h4, h4']
      have hz0 : ((0 : DirectSum (EdgeChoice.CosetIndex Γ (ch i j ε'))
          (fun _ => hObj V WK i)) (σ⁻¹ • η')) = 0 := rfl
      rw [hz0, map_zero]
      rfl
  have hkey := phiEdgeBlock_balAct V WK hWK ch i j (σ : Gal(L/K)) σ.2 z
  rw [hbal, hz] at hkey
  exact hkey

/-- The coset `η` is `rep η` applied to the base coset.  @census none (helper) -/
theorem EdgeChoice.smul_cosetOne {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch) :
    (⟨EdgeChoice.rep Γ ch η, ch.rep_mem η⟩ :
        ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) • EdgeChoice.cosetOne ch = η := by
  have h1 : (⟨EdgeChoice.rep Γ ch η, ch.rep_mem η⟩ :
      ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) = Quotient.out η := Subtype.ext rfl
  rw [h1]
  show QuotientGroup.mk (Quotient.out η * 1) = η
  rw [mul_one]
  exact Quotient.out_eq η

/-- `τ_ε · rep η₀ · τ_ε⁻¹` stabilises `e_ε`.  @census none (helper) -/
theorem EdgeChoice.tau_cosetOne_mem {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) :
    (ch.τ * EdgeChoice.rep Γ ch (EdgeChoice.cosetOne ch) * ch.τ⁻¹) • Γ.edgeRep ε
      = Γ.edgeRep ε := by
  rw [mul_smul, mul_smul,
    show EdgeChoice.rep Γ ch (EdgeChoice.cosetOne ch) • (ch.τ⁻¹ • Γ.edgeRep ε)
      = ch.τ⁻¹ • Γ.edgeRep ε from EdgeChoice.rep_cosetOne_mem ch,
    smul_smul, mul_inv_cancel, one_smul]

/-- **Step 3b**: on the `K`-form, `phiEdgeAt` at any coset is `phiEdgeRep` twisted by `η τ_ε⁻¹` —
which is exactly the twist `Φ_{ij}`'s `(ε,η)`-component carries.  @census none (helper) -/
theorem phiEdgeAt_kForm {i j : Γ.VertexOrbit}
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch i j ε)) (w : ↥(WK i)) :
    phiEdgeAt V WK hWK ch i j ε η ((1 : L) ⊗ₜ[K] w)
      = hPhi V WK (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹) j
          (phiEdgeRep V WK hWK ch i j ε ((1 : L) ⊗ₜ[K] w)) := by
  have hfix : ∀ g : Gal(L/K),
      hPhi V WK g i ((1 : L) ⊗ₜ[K] w) = (1 : L) ⊗ₜ[K] w := by
    intro g; rw [hPhi_tmul, map_one]
  -- move from the base coset to `η`
  have h3a := phiEdgeAt_smul_index V WK hWK ch ε (EdgeChoice.cosetOne (ch i j ε))
    ⟨EdgeChoice.rep Γ (ch i j ε) η, (ch i j ε).rep_mem η⟩ ((1 : L) ⊗ₜ[K] w)
  rw [EdgeChoice.smul_cosetOne, hfix] at h3a
  rw [h3a]
  -- `phiEdgeRep` on the `K`-form is `phiEdgeAt` at the base coset, untwisted
  have hbase : phiEdgeAt V WK hWK ch i j ε (EdgeChoice.cosetOne (ch i j ε))
        ((1 : L) ⊗ₜ[K] w)
      = hPhi V WK ((ch i j ε).baseTrans) j
          (phiEdgeRep V WK hWK ch i j ε ((1 : L) ⊗ₜ[K] w)) := by
    rw [phiEdgeRep_tmul, one_smul, AddEquiv.apply_symm_apply]
  rw [hbase, hPhi_comp]
  -- the two twists differ by an element of `G_{e_ε}`, which `phiEdgeRep` absorbs
  have hk : ((ch i j ε).τ * EdgeChoice.rep Γ (ch i j ε) (EdgeChoice.cosetOne (ch i j ε))
      * (ch i j ε).τ⁻¹) • Γ.edgeRep ε = Γ.edgeRep ε := EdgeChoice.tau_cosetOne_mem (ch i j ε)
  have hsplit : EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).baseTrans
      = (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹) *
        ((ch i j ε).τ * EdgeChoice.rep Γ (ch i j ε) (EdgeChoice.cosetOne (ch i j ε))
          * (ch i j ε).τ⁻¹) := by
    simp only [EdgeChoice.baseTrans]
    group
  rw [hsplit, ← hPhi_comp,
    phiEdgeRep_equivariant V WK hWK ch i j ε _ hk, hfix]

/-- `edgeSummandKRat` on a generator: the `L_i`-scalar crosses as `σ_ε` — the structure map
`L_i → L(e_ε)` is "apply `σ_ε`" (`edgeComponentLeft_coe_sigma`).  @census none (helper) -/
theorem edgeSummandKRat_mk {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (h : IsKRationalStructure V i (WK i)) (x : ↥(Γ.edgeOrbitField ε))
    (c : Γ.toSpecies.L i) (w : ↥(WK i)) :
    edgeSummandKRat V WK ε h
        (edgeSummandMkG (V.W i) ε x (kRatEquiv V WK h (c ⊗ₜ[K] w)))
      = ((Γ.edgeComponentLeft ε c) * x) ⊗ₜ[K] w := by
  letI := edgeLeftAlgebraSpecies ε
  haveI : IsScalarTower K (Γ.toSpecies.L i) ↥(Γ.edgeOrbitField ε) :=
    IsScalarTower.of_algebraMap_eq fun d =>
      ((Γ.edgeComponentLeft ε).commutes d).symm
  show (TensorProduct.AlgebraTensorModule.cancelBaseChange
      K (Γ.toSpecies.L i) ↥(Γ.edgeOrbitField ε) ↥(Γ.edgeOrbitField ε) ↥(WK i))
      (x ⊗ₜ[Γ.toSpecies.L i]
        ((kRatEquiv V WK h).symm (kRatEquiv V WK h (c ⊗ₜ[K] w)))) = _
  rw [LinearEquiv.symm_apply_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
  congr 1

/-- **Step 3c**: the `(ε,η)`-summand of `f' ⊗ 1_L`, on a generator, **is** `Φ_{ij}`'s
`(ε,η)`-component for `H.obj V`.  This is the match `H2`(a) is about, and the `σ_ε` on the two
sides is the same `σ_ε` — the species structure map `L_i → L(e_ε)` (`edgeComponentLeft_coe_sigma`)
on the right, `EdgeChoice`'s `σ_ε` on the left.  @census none (helper) -/
theorem phiEdgeAt_wiiMjL2_generator {i j : Γ.VertexOrbit}
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch i j ε))
    (x : ↥(Γ.edgeOrbitField ε)) (c : Γ.toSpecies.L i) (w : ↥(WK i)) :
    phiEdgeAt V WK hWK ch i j ε η
        (wiiMjL2Summand V WK ε
          (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹) (hWK i)
          (Twist.ofL (1 : L) ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε)
              (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹)]
            edgeSummandMkG (V.W i) ε x (kRatEquiv V WK (hWK i) (c ⊗ₜ[K] w))))
      = (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹) ((x : L))
          • hPhi V WK (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹) j
              (phiEdgeRep V WK hWK ch i j ε
                (hPhi V WK (ch i j ε).σ i
                  ((algebraMap (Γ.toSpecies.L i) L c) ⊗ₜ[K] w))) := by
  rw [wiiMjL2Summand_ofL, edgeSummandKRat_mk, twistAbsorb_tmul, one_mul]
  -- left: `ρ(σ_ε c · x) ⊗ w`, and `phiEdgeAt` is `L`-linear
  have hsig : ((Γ.edgeComponentLeft ε c : ↥(Γ.edgeOrbitField ε)) : L)
      = (ch i j ε).σ (algebraMap (Γ.toSpecies.L i) L c) :=
    edgeComponentLeft_coe_sigma (ch i j ε) c
  have hL : ((EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹)
        (((Γ.edgeComponentLeft ε c) * x : ↥(Γ.edgeOrbitField ε)) : L)) ⊗ₜ[K] w
      = ((EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹) ((x : L))
          * (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹)
              ((ch i j ε).σ (algebraMap (Γ.toSpecies.L i) L c)))
        • ((1 : L) ⊗ₜ[K] w) := by
    rw [show (((Γ.edgeComponentLeft ε c) * x : ↥(Γ.edgeOrbitField ε)) : L)
        = ((Γ.edgeComponentLeft ε c : ↥(Γ.edgeOrbitField ε)) : L) * ((x : L)) from rfl,
      map_mul, hsig, mul_comm]
    show _ = (_ : L) ⊗ₜ[K] w
    rw [smul_eq_mul, mul_one]
  rw [hL, map_smul, phiEdgeAt_kForm, mul_smul]
  congr 1
  rw [hPhi_tmul]
  rw [show (ch i j ε).σ ((algebraMap (Γ.toSpecies.L i) L) c) ⊗ₜ[K] w
      = ((ch i j ε).σ ((algebraMap (Γ.toSpecies.L i) L) c)) • ((1 : L) ⊗ₜ[K] w) from by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
  rw [LinearMap.map_smul, hPhi_smul]

/-- **Step 3d(A)**: `phiEdgeBlock` is the double sum of its `(ε,η)`-restrictions.
@census none (helper) -/
theorem phiEdgeBlock_sum {i j : Γ.VertexOrbit}
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (x : ⨁ ε : Γ.EdgeOrbit i j,
      ⨁ _η : EdgeChoice.CosetIndex Γ (ch i j ε), hObj V WK i) :
    phiEdgeBlock V WK hWK ch i j x
      = ∑ ε : Γ.EdgeOrbit i j, ∑ η : EdgeChoice.CosetIndex Γ (ch i j ε),
          phiEdgeAt V WK hWK ch i j ε η ((x ε) η) := by
  conv_lhs => rw [← DirectSum.sum_univ_of x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  conv_lhs => rw [← DirectSum.sum_univ_of (x ε)]
  rw [← DirectSum.lof_eq_of L, map_sum, map_sum]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [← DirectSum.lof_eq_of L]
  rfl

/-- **Step 3d(B)**: `phiEdgeBlock` after `wiiMjL2Equiv` is `f' ⊗ 1_L` landed by `kFormIncl`.
@census none (helper) -/
theorem phiEdgeBlock_generator {i j : Γ.VertexOrbit}
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (w₀ : V.W i) (m : Γ.toSpecies.M i j) :
    phiEdgeBlock V WK hWK ch i j
        (wiiMjL2Equiv V i j WK hWK ch (Balanced.mk (Balanced.mk w₀ m) (1 : L)))
      = kFormIncl V WK j (hWK j)
          (EtaleSpecies.Rep.f' Γ.toSpecies V i j (Balanced.mk w₀ m)) := by
  show balancedKRat V WK j (hWK j) (fPrimeBaseChange V i j
      ((wiiMjL2Equiv V i j WK hWK ch).symm
        (wiiMjL2Equiv V i j WK hWK ch (Balanced.mk (Balanced.mk w₀ m) (1 : L))))) = _
  rw [LinearEquiv.symm_apply_apply]
  show balancedKRat V WK j (hWK j)
      (Balanced.mk (EtaleSpecies.Rep.f' Γ.toSpecies V i j (Balanced.mk w₀ m)) (1 : L)) = _
  show hObjEquivBaseChange V WK j (hWK j)
      ((1 : L) ⊗ₜ[Γ.toSpecies.L j]
        (EtaleSpecies.Rep.f' Γ.toSpecies V i j (Balanced.mk w₀ m))) = _
  rw [kFormIncl_eq]

/-- `kFormIncl` on a `C4` generator.  @census none (helper) -/
theorem kFormIncl_kRatEquiv_tmul {i : Γ.VertexOrbit} (h : IsKRationalStructure V i (WK i))
    (c : Γ.toSpecies.L i) (w : ↥(WK i)) :
    kFormIncl V WK i h (kRatEquiv V WK h (c ⊗ₜ[K] w))
      = (algebraMap (Γ.toSpecies.L i) L c) ⊗ₜ[K] w := by
  show LinearMap.rTensor _ _ ((kRatEquiv V WK h).symm (kRatEquiv V WK h (c ⊗ₜ[K] w))) = _
  rw [LinearEquiv.symm_apply_apply, LinearMap.rTensor_tmul]
  rfl

/-- **Step 3c at a general `w₀`** — 3c plus additivity through `kRatEquiv`.
@census none (helper) -/
theorem phiEdgeAt_wiiMjL2_general {i j : Γ.VertexOrbit}
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch i j ε))
    (w₀ : V.W i) (m : Γ.toSpecies.M i j) :
    phiEdgeAt V WK hWK ch i j ε η
        (wiiMjL2Equiv V i j WK hWK ch (Balanced.mk (Balanced.mk w₀ m) (1 : L)) ε η)
      = (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹) (((m ε : ↥(Γ.edgeOrbitField ε)) : L))
          • hPhi V WK (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹) j
              (phiEdgeRep V WK hWK ch i j ε
                (hPhi V WK (ch i j ε).σ i (kFormIncl V WK i (hWK i) w₀))) := by
  letI := edgeLeftAlgebraSpecies ε
  rw [wiiMjL2Equiv_apply]
  obtain ⟨t, rfl⟩ : ∃ t, kRatEquiv V WK (hWK i) t = w₀ :=
    ⟨(kRatEquiv V WK (hWK i)).symm w₀, LinearEquiv.apply_symm_apply _ _⟩
  induction t using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, show edgeSummandMkG (V.W i) ε (m ε) (0 : V.W i) = 0 from
        TensorProduct.tmul_zero _ _, TensorProduct.tmul_zero, map_zero, map_zero,
        kFormIncl_eq, TensorProduct.tmul_zero, map_zero, map_zero, map_zero, map_zero,
        smul_zero]
  | tmul c w =>
      rw [kFormIncl_kRatEquiv_tmul]
      exact phiEdgeAt_wiiMjL2_generator V WK hWK ch ε η (m ε) c w
  | add p q hp hq =>
      rw [map_add, show edgeSummandMkG (V.W i) ε (m ε)
          (kRatEquiv V WK (hWK i) p + kRatEquiv V WK (hWK i) q)
          = edgeSummandMkG (V.W i) ε (m ε) (kRatEquiv V WK (hWK i) p)
            + edgeSummandMkG (V.W i) ε (m ε) (kRatEquiv V WK (hWK i) q) from
        TensorProduct.tmul_add _ _ _,
        TensorProduct.tmul_add, map_add, map_add, hp, hq,
        show kFormIncl V WK i (hWK i) (kRatEquiv V WK (hWK i) p
            + kRatEquiv V WK (hWK i) q)
          = kFormIncl V WK i (hWK i) (kRatEquiv V WK (hWK i) p)
            + kFormIncl V WK i (hWK i) (kRatEquiv V WK (hWK i) q) from map_add _ _ _,
        map_add, map_add, map_add, smul_add]

/-- `hObjCast` cancels its own inverse.  @census none (helper) -/
@[simp] theorem hObjCast_symm_cast {i i' : Γ.VertexOrbit} (h : i = i') (x : hObj V WK i') :
    hObjCast V WK h (hObjCast V WK h.symm x) = x := by subst h; rfl

/-- `hObjCast` commutes with finite sums.  @census none (helper) -/
theorem hObjCast_sum {i i' : Γ.VertexOrbit} (h : i = i') {α : Type*} (s : Finset α)
    (f : α → hObj V WK i) :
    hObjCast V WK h (∑ a ∈ s, f a) = ∑ a ∈ s, hObjCast V WK h (f a) := by
  subst h; rfl

/-- `e_fix`'s inverse is its forward map.  @census none (helper) -/
theorem eFix_symm_apply
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (i : Γ.VertexOrbit) (y : V.W i) :
    (eFix V WK hWK ch i).symm y = eFixFwd V WK hWK ch i y := rfl

/-- **Clause `RQ2-2.28-H2`(a)** — the descent of `H.obj V`'s edge maps is `V`'s own structure map,
read through `e_fix`.  @census none (clause witness for `RQ2-2.28-H2`) -/
theorem hObjRep_edgeDescent_eq {i j : Γ.VertexOrbit}
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (chij : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₀ : wiiMjL (hObjRep V WK hWK ch).toRep i j
      ≃ₗ[L] wiiMjLpreRhs (hObjRep V WK hWK ch).toRep chij)
    (fH : EtaleSpecies.Rep.tensor Γ.toSpecies i j
            ↥((hObjRep V WK hWK ch).toRep.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ]
            ↥((hObjRep V WK hWK ch).toRep.vertexFixed (Γ.vertexRep j)))
    (hd : IsEdgeDescent (hObjRep V WK hWK ch).toRep chij e₀ fH)
    (w : ↥((hObjRep V WK hWK ch).toRep.vertexFixed (Γ.vertexRep i)))
    (m : Γ.toSpecies.M i j) :
    eFix V WK hWK ch j (fH (Balanced.mk w m))
      = EtaleSpecies.Rep.f' Γ.toSpecies V i j
          (Balanced.mk (eFix V WK hWK ch i w) m) := by
  -- reduce to the construction's own choice
  obtain ⟨e₁, h₁⟩ := wiiMj_baseChange_pre (hObjRep V WK hWK ch).toRep i j (ch i j)
  have hd₁ := isEdgeDescent_edgeDescentMap (hObjRep V WK hWK ch).toRep (ch i j) e₁ h₁
  have hfeq : fH = edgeDescentMap (hObjRep V WK hWK ch).toRep (ch i j) e₁ h₁ :=
    edgeDescent_choice_indep (hObjRep V WK hWK ch).toRep chij (ch i j) e₀ e₁ fH _ hd hd₁
  subst hfeq
  -- transpose along `e_fix`
  set w₀ := eFix V WK hWK ch i w with hw₀
  have hwv : eFixFwd V WK hWK ch i w₀ = w := by
    rw [hw₀, ← eFix_symm_apply, LinearEquiv.symm_apply_apply]
  refine (eFix V WK hWK ch j).symm.injective ?_
  rw [LinearEquiv.symm_apply_apply, eFix_symm_apply]
  refine Subtype.ext ?_
  refine (hObjCast V WK (Γ.vertexClass_vertexRep j)).injective ?_
  -- the right-hand side is `kFormIncl` of `f'`
  have hR : hObjCast V WK (Γ.vertexClass_vertexRep j)
      ((eFixFwd V WK hWK ch j (EtaleSpecies.Rep.f' Γ.toSpecies V i j
          (Balanced.mk w₀ m)) : (hObjRep V WK hWK ch).toRep.M (Γ.vertexRep j)))
      = kFormIncl V WK j (hWK j)
          (EtaleSpecies.Rep.f' Γ.toSpecies V i j (Balanced.mk w₀ m)) :=
    hObjCast_symm_cast V WK _ _
  rw [hR, ← phiEdgeBlock_generator V WK hWK ch w₀ m, phiEdgeBlock_sum]
  -- the left-hand side is the double sum of `phiComp`s
  have hval := hd₁.2 (phiTotal (hObjRep V WK hWK ch).toRep (ch i j))
    (phiTotal_single (hObjRep V WK hWK ch).toRep (ch i j)) (Balanced.mk w m) 1
  rw [phiTotal_e0_generator (hObjRep V WK hWK ch).toRep (ch i j) e₁ h₁ w m 1,
    one_smul] at hval
  have hpush : ∀ {α : Type u} (s : Finset α)
      (f : α → (hObjRep V WK hWK ch).toRep.M (Γ.vertexRep j)),
      hObjCast V WK (Γ.vertexClass_vertexRep j) (∑ a ∈ s, f a)
        = ∑ a ∈ s, hObjCast V WK (Γ.vertexClass_vertexRep j) (f a) := by
    intro α s f
    exact map_sum (hObjCast V WK (Γ.vertexClass_vertexRep j)) f s
  rw [← hval]
  refine Eq.trans (hpush Finset.univ _) ?_
  refine Finset.sum_congr rfl fun ε _ => ?_
  refine Eq.trans (hpush Finset.univ _) ?_
  refine Finset.sum_congr rfl fun η _ => ?_
  have hsmul : ∀ (a : L) (x : (hObjRep V WK hWK ch).toRep.M (Γ.vertexRep j)),
      hObjCast V WK (Γ.vertexClass_vertexRep j) (a • x)
        = a • hObjCast V WK (Γ.vertexClass_vertexRep j) x :=
    fun a x => hObjCast_smul V WK _ a x
  refine Eq.trans (hsmul _ _) ?_
  have harg : hObjCast V WK (Γ.vertexClass_vertexRep i)
      ((w : (hObjRep V WK hWK ch).toRep.M (Γ.vertexRep i)))
      = kFormIncl V WK i (hWK i) w₀ := by
    rw [← hwv]
    exact hObjCast_symm_cast V WK _ _
  rw [phiComp_hObjRep_read, phiEdgeAt_wiiMjL2_general V WK hWK ch ε η w₀ m,
    one_mul, harg]

end EFix

/-! ### `H` on morphisms — the vertex map  (G4)

`H.map φ` at a vertex is the base change of `ψ_i` along `− ⊗_{L_i} L`, transported through clause
`C4`: `M(v_i) = L ⊗_K W_{i,K} ≅ L ⊗_{L_i} W_i`, and `1 ⊗ ψ_i` there.  **It never touches the
`K`-forms**, which is why the fact that `ψ` need not map `W_{i,K}^U` into `W_{i,K}^V` is not an
obstruction — the risk I flagged before the probe, and the one that turned out not to bite.

What *does* bite is the twist: `hMapVertex` intertwines `hPhi h` only for `h ∈ G_{v_i}`
(`hObjEquivBaseChange_gal`'s hypothesis), because that is exactly when `h` fixes `L_i` and
`galLinearVOF` exists.  The `(ε,η)`-summand identification of `eq:WiiMjL2` carries the twist
`ρ_η σ_ε ∉ G_{v_i}` (`twistAbsorb_tmul`), so the naturality square for the chain closes with the
**twisted** base change and not the plain one.

`hMapVertex_kForm` is the computation the whole naturality argument runs on: on a `K`-form
generator the base change is `kFormIncl` of `ψ`'s value — the two descriptions of `e_fix`'s forward
map (§62.6) meeting the morphism map.

@census none (G4 engine for `RQ2-2.28-C5`)
-/

section HMap
variable {U V : EtaleSpecies.Rep Γ.toSpecies}
  (WKU : ∀ i : Γ.VertexOrbit, Submodule K (U.W i))
  (WKV : ∀ i : Γ.VertexOrbit, Submodule K (V.W i))
  (hU : ∀ k : Γ.VertexOrbit, IsKRationalStructure U k (WKU k))
  (hV : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WKV k))

/-- `ψ_i` read `L_i`-linearly: the two actions are the same action through `RingEquiv.toOpposite`. -/
noncomputable def psiL (ψ : Species.Rep.Hom U V) (i : Γ.VertexOrbit) :
    U.W i →ₗ[Γ.toSpecies.L i] V.W i where
  toFun := ψ.ψ i
  map_add' := map_add _
  map_smul' c x := (ψ.ψ i).map_smul (MulOpposite.op c) x

/-- `ψ_i` base-changed along `− ⊗_{L_i} L`. -/
noncomputable def psiBase (ψ : Species.Rep.Hom U V) (i : Γ.VertexOrbit) :
    (L ⊗[Γ.toSpecies.L i] (U.W i)) →ₗ[L] (L ⊗[Γ.toSpecies.L i] (V.W i)) :=
  TensorProduct.AlgebraTensorModule.map (LinearEquiv.refl L L).toLinearMap (psiL ψ i)

/-- **`H` on morphisms, at a vertex**: `1 ⊗ ψ_i` read through clause `C4`. -/
noncomputable def hMapVertex (ψ : Species.Rep.Hom U V) (i : Γ.VertexOrbit) :
    hObj U WKU i →ₗ[L] hObj V WKV i :=
  (hObjEquivBaseChange V WKV i (hV i)).toLinearMap ∘ₗ psiBase ψ i ∘ₗ
    (hObjEquivBaseChange U WKU i (hU i)).symm.toLinearMap

/-- **The computation the naturality argument runs on**: on a `K`-form generator the base change
is `kFormIncl` of `ψ`'s value. -/
theorem hMapVertex_kForm (ψ : Species.Rep.Hom U V) (i : Γ.VertexOrbit)
    (w : ↥(WKU i)) :
    hMapVertex WKU WKV hU hV ψ i ((1 : L) ⊗ₜ[K] w)
      = kFormIncl V WKV i (hV i) (ψ.ψ i ((w : U.W i))) := by
  have h1 : (kRatEquiv U WKU (hU i)).symm ((w : U.W i)) = (1 : Γ.toSpecies.L i) ⊗ₜ[K] w := by
    refine (kRatEquiv U WKU (hU i)).injective ?_
    rw [LinearEquiv.apply_symm_apply]
    show _ = (1 : Γ.toSpecies.L i) • ((w : U.W i))
    rw [one_smul]
  have h2 : kFormIncl U WKU i (hU i) ((w : U.W i)) = (1 : L) ⊗ₜ[K] w := by
    show LinearMap.rTensor _ _ ((kRatEquiv U WKU (hU i)).symm ((w : U.W i))) = _
    rw [h1, LinearMap.rTensor_tmul]
    show (algebraMap (Γ.toSpecies.L i) L 1) ⊗ₜ[K] w = _
    rw [map_one]
  rw [← h2, kFormIncl_eq]
  show hObjEquivBaseChange V WKV i (hV i) (psiBase ψ i
    ((hObjEquivBaseChange U WKU i (hU i)).symm
      (hObjEquivBaseChange U WKU i (hU i) ((1 : L) ⊗ₜ[Γ.toSpecies.L i] ((w : U.W i)))))) = _
  rw [LinearEquiv.symm_apply_apply, kFormIncl_eq]
  rfl

/-- **`hMapVertex` on `kFormIncl`'s image**, for an arbitrary `W_i`-element — the general form of
`hMapVertex_kForm`, and the one the naturality argument uses. -/
theorem hMapVertex_kFormIncl (ψ : Species.Rep.Hom U V) (i : Γ.VertexOrbit) (z : U.W i) :
    hMapVertex WKU WKV hU hV ψ i (kFormIncl U WKU i (hU i) z)
      = kFormIncl V WKV i (hV i) (ψ.ψ i z) := by
  rw [kFormIncl_eq, kFormIncl_eq]
  show hObjEquivBaseChange V WKV i (hV i) (psiBase ψ i
    ((hObjEquivBaseChange U WKU i (hU i)).symm
      (hObjEquivBaseChange U WKU i (hU i) ((1 : L) ⊗ₜ[Γ.toSpecies.L i] z)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end HMap

/-! ### The `(ε,η)`-summand read through `kFormIncl` — where the twist lives  (G4)

`wiiMjL2Summand_kFormIncl` is the statement that made the naturality question answerable:

```
wiiMjL2Summand ε ρ (ofL a ⊗ (x ⊗_{L_i} z))  =  (a · ρ x) • φ_{ρ σ_ε} (kFormIncl z).
```

The summand is `kFormIncl` of `z` **twisted by `ρ σ_ε`** — not `kFormIncl` of `z`.  That is
`twistAbsorb`'s `ρ` composed with `edgeSummandKRat`'s `σ_ε` (§62.13), collected into one group
element, and it is the exact reason the naturality square for `eq:WiiMjL2` commutes against the
twisted diagonal `⊕_{ε,η} Ψ^{ρ_η σ_ε}` rather than against `⊕ Ψ`.

**Booked for `RQ2-2.29`'s assembly** (which consumes both functors): the `H`-side chain is natural,
but the intertwiner it carries on `⊕_ε ⊕_η M(v_i)` is the **twisted** one.  Any argument that pairs
`F` and `H` and needs `eq:WiiMjL2` to be natural must use `Ψ^{ρ_η σ_ε}`; the plain `Ψ` makes a
square that does not commute, and it will not announce itself — the two sides differ by a Galois
twist on the `L_i`-scalar and both typecheck.

@census none (G4 engine for `RQ2-2.28-C5`)
-/

section SummandTwist
variable (V : EtaleSpecies.Rep Γ.toSpecies)
  (WK : ∀ i : Γ.VertexOrbit, Submodule K (V.W i))

/-- **The `(ε,η)`-summand is `kFormIncl` twisted by `ρ σ_ε`.**  `twistAbsorb`'s `ρ` and
`edgeSummandKRat`'s `σ_ε` collected into one group element.  @census none (helper) -/
theorem wiiMjL2Summand_kFormIncl {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (ch : Γ.EdgeChoice ε) (ρ : Gal(L/K)) (h : IsKRationalStructure V i (WK i))
    (a : L) (x : ↥(Γ.edgeOrbitField ε)) (z : V.W i) :
    wiiMjL2Summand V WK ε ρ h
        (Twist.ofL a ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ]
          edgeSummandMkG (V.W i) ε x z)
      = (a * ρ ((x : L))) • hPhi V WK (ρ * ch.σ) i (kFormIncl V WK i h z) := by
  letI := edgeLeftAlgebraSpecies ε
  obtain ⟨t, rfl⟩ : ∃ t, kRatEquiv V WK h t = z :=
    ⟨(kRatEquiv V WK h).symm z, LinearEquiv.apply_symm_apply _ _⟩
  induction t using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, show edgeSummandMkG (V.W i) ε x (0 : V.W i) = 0 from
        TensorProduct.tmul_zero _ _, TensorProduct.tmul_zero, map_zero,
        kFormIncl_eq, TensorProduct.tmul_zero, map_zero, map_zero, smul_zero]
  | tmul c w =>
      rw [wiiMjL2Summand_ofL, edgeSummandKRat_mk, twistAbsorb_tmul,
        kFormIncl_kRatEquiv_tmul, hPhi_tmul]
      show (a * ρ (((Γ.edgeComponentLeft ε c : ↥(Γ.edgeOrbitField ε)) : L) * ((x : L))))
          ⊗ₜ[K] w = _
      rw [map_mul, edgeComponentLeft_coe_sigma ch c, AlgEquiv.mul_apply,
        TensorProduct.smul_tmul', smul_eq_mul]
      show (a * (ρ (ch.σ (algebraMap (Γ.toSpecies.L i) L c)) * ρ ((x : L)))) ⊗ₜ[K] w
          = (a * ρ ((x : L)) * ρ (ch.σ (algebraMap (Γ.toSpecies.L i) L c))) ⊗ₜ[K] w
      rw [show a * (ρ (ch.σ (algebraMap (Γ.toSpecies.L i) L c)) * ρ ((x : L)))
          = a * ρ ((x : L)) * ρ (ch.σ (algebraMap (Γ.toSpecies.L i) L c)) from by ring]
  | add p q hp hq =>
      rw [map_add, show edgeSummandMkG (V.W i) ε x
          (kRatEquiv V WK h p + kRatEquiv V WK h q)
          = edgeSummandMkG (V.W i) ε x (kRatEquiv V WK h p)
            + edgeSummandMkG (V.W i) ε x (kRatEquiv V WK h q) from
        TensorProduct.tmul_add _ _ _,
        TensorProduct.tmul_add, map_add, hp, hq,
        show kFormIncl V WK i h (kRatEquiv V WK h p + kRatEquiv V WK h q)
          = kFormIncl V WK i h (kRatEquiv V WK h p)
            + kFormIncl V WK i h (kRatEquiv V WK h q) from map_add _ _ _,
        map_add, smul_add]

end SummandTwist

/-! ### The twisted intertwiner, and the chain's naturality  (G4)

`eq:WiiMjL2` is natural in the representation, but **against the twisted diagonal**: the
`(ε,η)`-summand identification carries `ρ_η σ_ε` (§62.16), so the map on `⊕_ε ⊕_η M(v_i)` induced
by `ψ` is `⊕_{ε,η} Ψ^{ρ_η σ_ε}` where

```
Ψ^g := φ_g ∘ hMapVertex ∘ φ_g^{-1}
```

is `L`-linear because the two semi-linear factors cancel — the `phiEdgeConj` pattern for the third
time in this row (`phiEdgeConj`, `psiTwist`, and `hPhi_fix_symm`'s conjugation before it).

With `wiiMjL2Summand_kFormIncl` and `hMapVertex_kFormIncl` in hand the square is a two-line
computation on generators, and `balanced_addHom_ext` finishes: **nothing is inverted**, which is
route (C)'s technique used a third time and for the third time cheaper than the alternative.

@census none (G4 engine for `RQ2-2.28-C5`)
-/

section ChainNat
variable {U V : EtaleSpecies.Rep Γ.toSpecies}
  (WKU : ∀ i : Γ.VertexOrbit, Submodule K (U.W i))
  (WKV : ∀ i : Γ.VertexOrbit, Submodule K (V.W i))
  (hU : ∀ k : Γ.VertexOrbit, IsKRationalStructure U k (WKU k))
  (hV : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WKV k))

/-- **The twisted base change** `Ψ^g`.  `L`-linear: the two semi-linear factors cancel. -/
noncomputable def psiTwist (ψ : Species.Rep.Hom U V) (g : Gal(L/K)) (i : Γ.VertexOrbit) :
    hObj U WKU i →ₗ[L] hObj V WKV i where
  toFun y := hPhi V WKV g i (hMapVertex WKU WKV hU hV ψ i (hPhi U WKU g⁻¹ i y))
  map_add' y y' := by rw [map_add, map_add, map_add]
  map_smul' c y := by
    show hPhi V WKV g i (hMapVertex WKU WKV hU hV ψ i (hPhi U WKU g⁻¹ i (c • y))) = _
    rw [hPhi_smul, LinearMap.map_smul, hPhi_smul]
    show (g (g⁻¹ c)) • _ = _
    rw [show g (g⁻¹ c) = c from congrArg (fun t : Gal(L/K) => t c) (mul_inv_cancel g)]
    rfl

/-- `Ψ^g` undoes the twist it is given.  @census none (helper) -/
theorem psiTwist_hPhi (ψ : Species.Rep.Hom U V) (g : Gal(L/K)) (i : Γ.VertexOrbit)
    (z : U.W i) :
    psiTwist WKU WKV hU hV ψ g i (hPhi U WKU g i (kFormIncl U WKU i (hU i) z))
      = hPhi V WKV g i (kFormIncl V WKV i (hV i) (ψ.ψ i z)) := by
  show hPhi V WKV g i (hMapVertex WKU WKV hU hV ψ i
    (hPhi U WKU g⁻¹ i (hPhi U WKU g i (kFormIncl U WKU i (hU i) z)))) = _
  rw [hPhi_comp, inv_mul_cancel, hPhi_one, hMapVertex_kFormIncl]

/-- `ψ` on `W_i ⊗_{L_i} {}_iM_j ⊗_{L_j} L`.  @census none (helper) -/
noncomputable def hMapTensor (ψ : Species.Rep.Hom U V) (i j : Γ.VertexOrbit) :
    Balanced K (Γ.toSpecies.L j) L L
        (EtaleSpecies.Rep.tensor Γ.toSpecies i j (U.W i))
      →ₗ[Lᵐᵒᵖ] Balanced K (Γ.toSpecies.L j) L L
        (EtaleSpecies.Rep.tensor Γ.toSpecies i j (V.W i)) :=
  Balanced.map (fun c x => Balanced.smul_K (A := Γ.toSpecies.L i) c x)
    (fun c x => Balanced.smul_K (A := Γ.toSpecies.L i) c x)
    (Balanced.map (K := K) (A := Γ.toSpecies.L i) (Y := Γ.toSpecies.M i j)
      (U.smul_K_W i) (V.smul_K_W i) (ψ.ψ i) (Γ.toSpecies.L j)) L

open scoped Classical in
/-- **`eq:WiiMjL2` is natural — against the twisted diagonal.**  @census none (helper) -/
theorem wiiMjL2Equiv_natural
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (ψ : Species.Rep.Hom U V) (i j : Γ.VertexOrbit)
    [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch i j ε))]
    (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch i j ε))
    (z : Balanced K (Γ.toSpecies.L j) L L
      (EtaleSpecies.Rep.tensor Γ.toSpecies i j (U.W i))) :
    wiiMjL2Equiv V i j WKV hV ch (hMapTensor ψ i j z) ε η
      = psiTwist WKU WKV hU hV ψ
          (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹ * (ch i j ε).σ) i
          (wiiMjL2Equiv U i j WKU hU ch z ε η) := by
  have key : (((DFinsupp.evalAddMonoidHom η).comp
        ((DFinsupp.evalAddMonoidHom ε).comp
          ((wiiMjL2Equiv V i j WKV hV ch).toLinearMap.toAddMonoidHom.comp
            (hMapTensor ψ i j).toAddMonoidHom)))
      = ((psiTwist WKU WKV hU hV ψ
            (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹ * (ch i j ε).σ)
            i).toAddMonoidHom.comp
          ((DFinsupp.evalAddMonoidHom η).comp
            ((DFinsupp.evalAddMonoidHom ε).comp
              (wiiMjL2Equiv U i j WKU hU ch).toLinearMap.toAddMonoidHom)))) := by
    refine balanced_addHom_ext fun t a => ?_
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective
      (balancedRel K (Γ.toSpecies.L i) (Γ.toSpecies.L j) (Γ.toSpecies.M i j) (U.W i)) t
    induction s with
    | zero =>
        rw [show (Submodule.Quotient.mk (0 : Γ.toSpecies.M i j ⊗[K] U.W i) :
          EtaleSpecies.Rep.tensor Γ.toSpecies i j (U.W i)) = 0 from rfl,
          show Balanced.mk (K := K) (A := Γ.toSpecies.L j) (B := L)
            (0 : EtaleSpecies.Rep.tensor Γ.toSpecies i j (U.W i)) a = 0 from
            Balanced.mk_zero_left a]
        simp
    | tmul m z0 =>
        show wiiMjL2Equiv V i j WKV hV ch
            (hMapTensor ψ i j (Balanced.mk (Balanced.mk z0 m) a)) ε η = _
        show wiiMjL2Equiv V i j WKV hV ch
            (Balanced.mk (Balanced.mk (ψ.ψ i z0) m) a) ε η = _
        rw [wiiMjL2Equiv_apply, wiiMjL2Summand_kFormIncl V WKV ε (ch i j ε)]
        show _ = psiTwist WKU WKV hU hV ψ _ i
          (wiiMjL2Equiv U i j WKU hU ch (Balanced.mk (Balanced.mk z0 m) a) ε η)
        rw [wiiMjL2Equiv_apply, wiiMjL2Summand_kFormIncl U WKU ε (ch i j ε),
          LinearMap.map_smul, psiTwist_hPhi]
    | add s t hs ht =>
        rw [show (Submodule.Quotient.mk (s + t) :
          EtaleSpecies.Rep.tensor Γ.toSpecies i j (U.W i))
            = Submodule.Quotient.mk s + Submodule.Quotient.mk t from rfl,
          Balanced.mk_add_left, map_add, map_add, hs, ht]
  exact DFunLike.congr_fun key z

end ChainNat

/-! ### `H` on morphisms — the family is indexed by VERTICES  (G4)

A correction worth stating plainly, because it is the second time in this row that a per-**orbit**
shape was the wrong first guess against a per-**vertex** definition (the first was the edge class:
`edgeClassAt` versus reading the orbit off the edge, §62.9).

`Rep.Hom`'s `ψ` is indexed by **vertices**, and its `rational` field —
`ψ_{σv} ∘ φ^M_{v,σ} = φ^N_{v,σ} ∘ ψ_v` — relates `ψ` at `v` and at `σ · v`, *different vertices of
one orbit*.  So `ψ` **may and must differ across a vertex orbit**, and `rational` is precisely the
statement that the family is a **conjugation family**.  A single map per orbit forces
`ψ_v = ψ_{σ v}`, which is false whenever `σ ∉ G_v`: `hMapVertex` commutes with `φ_g` only for
`g ∈ G_{v}` (the same boundary as `hObjEquivBaseChange_gal`'s hypothesis), so an orbit-indexed
`ψ` is not a morphism of `Rep` at all.

The right datum is therefore

```
ψ_v := Ψ^{g_v},     g_v · v_i = v,     i = vertexClass v,
```

with `ψ_{v_i} = hMapVertex_i`.  `rational` then holds **by the group law** — no edge machinery
enters — and well-definedness (independence of the chosen `g_v`) is exactly
`hMapVertex_gal`, i.e. `hObjEquivBaseChange_gal` on both sides.  The `Exists.choose` in `g_v`
washes out for the same reason `edgeTrans`'s did (§62.11).

**For S8: start vertex-indexed wherever the definition is vertex-indexed.**  Both times, the
orbit-indexed guess came from `hObj` being orbit-indexed — which is right for the *object* and
wrong for anything the definition quantifies per vertex.

@census none (G4 engine for `RQ2-2.28-C5`)
-/

/-- Every vertex is a translate of its orbit's representative.  @census none (helper) -/
theorem exists_smul_vertexRep (v : Γ.V) :
    ∃ g : Gal(L/K), g • Γ.vertexRep (Γ.vertexClass v) = v :=
  Quotient.exact (Γ.vertexClass_vertexRep (Γ.vertexClass v)).symm

/-- The chosen translation carrying `v_i` to `v`.  @census none (helper) -/
noncomputable def vertexTrans (v : Γ.V) : Gal(L/K) := (exists_smul_vertexRep v).choose

theorem vertexTrans_spec (v : Γ.V) :
    vertexTrans v • Γ.vertexRep (Γ.vertexClass v) = v := (exists_smul_vertexRep v).choose_spec

section HMapPsi
variable {U V : EtaleSpecies.Rep Γ.toSpecies}
  (WKU : ∀ i : Γ.VertexOrbit, Submodule K (U.W i))
  (WKV : ∀ i : Γ.VertexOrbit, Submodule K (V.W i))
  (hU : ∀ k : Γ.VertexOrbit, IsKRationalStructure U k (WKU k))
  (hV : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WKV k))

/-- **The well-definedness lemma**: `hMapVertex` commutes with `φ_k` for `k ∈ G_{v_i}`, because
that is exactly when `k` fixes `L_i`.  @census none (helper) -/
theorem hMapVertex_gal (ψ : Species.Rep.Hom U V) (i : Γ.VertexOrbit) (k : Gal(L/K))
    (hk : k • Γ.vertexRep i = Γ.vertexRep i) (y : hObj U WKU i) :
    hMapVertex WKU WKV hU hV ψ i (hPhi U WKU k i y)
      = hPhi V WKV k i (hMapVertex WKU WKV hU hV ψ i y) := by
  obtain ⟨t, rfl⟩ : ∃ t, hObjEquivBaseChange U WKU i (hU i) t = y :=
    ⟨(hObjEquivBaseChange U WKU i (hU i)).symm y, LinearEquiv.apply_symm_apply _ _⟩
  rw [← hObjEquivBaseChange_gal U WKU i (hU i) k hk t]
  show hObjEquivBaseChange V WKV i (hV i) (psiBase ψ i
      ((hObjEquivBaseChange U WKU i (hU i)).symm
        (hObjEquivBaseChange U WKU i (hU i)
          (LinearMap.rTensor (U.W i) (galLinearVOF i k hk) t)))) = _
  rw [LinearEquiv.symm_apply_apply]
  show _ = hPhi V WKV k i (hObjEquivBaseChange V WKV i (hV i) (psiBase ψ i
      ((hObjEquivBaseChange U WKU i (hU i)).symm
        (hObjEquivBaseChange U WKU i (hU i) t))))
  rw [LinearEquiv.symm_apply_apply, ← hObjEquivBaseChange_gal V WKV i (hV i) k hk]
  congr 1
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a z => rfl
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

/-- **The conjugation-family law** — `psiTwist`'s version of `phiEdgeConj_equivariant`, and the
whole of `Rep.Hom`'s `rational` field once the translations are supplied.  @census none (helper) -/
theorem psiTwist_conj (ψ : Species.Rep.Hom U V) (i : Γ.VertexOrbit) (g g' σ : Gal(L/K))
    (hk : (g'⁻¹ * σ * g) • Γ.vertexRep i = Γ.vertexRep i) (y : hObj U WKU i) :
    psiTwist WKU WKV hU hV ψ g' i (hPhi U WKU σ i y)
      = hPhi V WKV σ i (psiTwist WKU WKV hU hV ψ g i y) := by
  show hPhi V WKV g' i (hMapVertex WKU WKV hU hV ψ i
      (hPhi U WKU g'⁻¹ i (hPhi U WKU σ i y)))
    = hPhi V WKV σ i (hPhi V WKV g i (hMapVertex WKU WKV hU hV ψ i (hPhi U WKU g⁻¹ i y)))
  rw [hPhi_comp, show g'⁻¹ * σ = (g'⁻¹ * σ * g) * g⁻¹ from by group, ← hPhi_comp,
    hMapVertex_gal WKU WKV hU hV ψ i _ hk, hPhi_comp, hPhi_comp]
  congr 2
  group

/-- **`H` on morphisms**: one map per **vertex**, the base change twisted by a translation
carrying `v_i` to `v`.  @census none (helper for `RQ2-2.28-C5`) -/
noncomputable def hMapPsi (ψ : Species.Rep.Hom U V) (v : Γ.V) :
    hObj U WKU (Γ.vertexClass v) →ₗ[L] hObj V WKV (Γ.vertexClass v) :=
  psiTwist WKU WKV hU hV ψ (vertexTrans v) (Γ.vertexClass v)

/-- `psiTwist` commutes with the orbit transport.  @census none (helper) -/
theorem psiTwist_hObjCast (ψ : Species.Rep.Hom U V) (g : Gal(L/K))
    {i i' : Γ.VertexOrbit} (h : i = i') (y : hObj U WKU i) :
    hObjCast V WKV h (psiTwist WKU WKV hU hV ψ g i y)
      = psiTwist WKU WKV hU hV ψ g i' (hObjCast U WKU h y) := by
  subst h; rfl

/-- **Clause `RQ2-1.09-C2` for `H.map`** — the `rational` field, holding by the group law.
@census none (clause witness for `RQ2-2.28-C5`) -/
theorem hMapPsi_rational (ψ : Species.Rep.Hom U V) (σ : Gal(L/K)) (v : Γ.V)
    (y : hObj U WKU (Γ.vertexClass v)) :
    hObjCast V WKV (vertexClass_smul σ v)
        (hMapPsi WKU WKV hU hV ψ (σ • v)
          (hObjCast U WKU (vertexClass_smul σ v).symm
            (hPhi U WKU σ (Γ.vertexClass v) y)))
      = hPhi V WKV σ (Γ.vertexClass v) (hMapPsi WKU WKV hU hV ψ v y) := by
  have hcl : Γ.vertexClass (σ • v) = Γ.vertexClass v := vertexClass_smul σ v
  have hg := vertexTrans_spec v
  have hg' := vertexTrans_spec (σ • v)
  rw [hcl] at hg'
  have hk : ((vertexTrans (σ • v))⁻¹ * σ * vertexTrans v)
      • Γ.vertexRep (Γ.vertexClass v) = Γ.vertexRep (Γ.vertexClass v) := by
    rw [mul_smul, mul_smul, hg, inv_smul_eq_iff]
    exact hg'.symm
  show hObjCast V WKV hcl (psiTwist WKU WKV hU hV ψ (vertexTrans (σ • v))
      (Γ.vertexClass (σ • v)) (hObjCast U WKU hcl.symm _)) = _
  rw [psiTwist_hObjCast, hObjCast_symm_cast,
    psiTwist_conj WKU WKV hU hV ψ (Γ.vertexClass v) (vertexTrans v)
      (vertexTrans (σ • v)) σ hk]
  rfl

/-- `psiTwist` depends only on `g · v_i`, not on `g` — the coset ambiguity is absorbed by
`hMapVertex_gal`.  @census none (helper) -/
theorem psiTwist_congr (ψ : Species.Rep.Hom U V) (i : Γ.VertexOrbit) (g g' : Gal(L/K))
    (h : g • Γ.vertexRep i = g' • Γ.vertexRep i) (y : hObj U WKU i) :
    psiTwist WKU WKV hU hV ψ g i y = psiTwist WKU WKV hU hV ψ g' i y := by
  have hk : (g'⁻¹ * g) • Γ.vertexRep i = Γ.vertexRep i := by
    rw [mul_smul, h, inv_smul_smul]
  show hPhi V WKV g i (hMapVertex WKU WKV hU hV ψ i (hPhi U WKU g⁻¹ i y))
    = hPhi V WKV g' i (hMapVertex WKU WKV hU hV ψ i (hPhi U WKU g'⁻¹ i y))
  rw [show g⁻¹ = (g'⁻¹ * g)⁻¹ * g'⁻¹ from by group, ← hPhi_comp,
    hMapVertex_gal WKU WKV hU hV ψ i _ (by
      rw [show ((g'⁻¹ * g)⁻¹ : Gal(L/K)) = (g'⁻¹ * g)⁻¹ from rfl, inv_smul_eq_iff, hk]),
    hPhi_comp, show g * (g'⁻¹ * g)⁻¹ = g' from by group]

/-- Naturality of clause `C4`'s identification.  @census none (helper) -/
theorem balancedKRat_natural (ψ : Species.Rep.Hom U V) (j : Γ.VertexOrbit)
    (t : Balanced K (Γ.toSpecies.L j) L L (U.W j)) :
    hMapVertex WKU WKV hU hV ψ j (balancedKRat U WKU j (hU j) t)
      = balancedKRat V WKV j (hV j)
          (Balanced.map (K := K) (A := Γ.toSpecies.L j) (Y := L)
            (U.smul_K_W j) (V.smul_K_W j) (ψ.ψ j) L t) := by
  have key : ((hMapVertex WKU WKV hU hV ψ j).toAddMonoidHom.comp
        (balancedKRat U WKU j (hU j)).toLinearMap.toAddMonoidHom)
      = ((balancedKRat V WKV j (hV j)).toLinearMap.toAddMonoidHom.comp
          (Balanced.map (K := K) (A := Γ.toSpecies.L j) (Y := L)
            (U.smul_K_W j) (V.smul_K_W j) (ψ.ψ j) L).toAddMonoidHom) := by
    refine balanced_addHom_ext fun x a => ?_
    show hMapVertex WKU WKV hU hV ψ j
        (hObjEquivBaseChange U WKU j (hU j) (a ⊗ₜ[Γ.toSpecies.L j] x)) = _
    show _ = balancedKRat V WKV j (hV j) (Balanced.mk (ψ.ψ j x) a)
    show _ = hObjEquivBaseChange V WKV j (hV j) (a ⊗ₜ[Γ.toSpecies.L j] (ψ.ψ j x))
    show hObjEquivBaseChange V WKV j (hV j) (psiBase ψ j
      ((hObjEquivBaseChange U WKU j (hU j)).symm
        (hObjEquivBaseChange U WKU j (hU j) (a ⊗ₜ[Γ.toSpecies.L j] x)))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  exact DFunLike.congr_fun key t

/-- **Naturality of `f' ⊗ 1_L`** — this *is* the species-morphism axiom, and the only place the
hypothesis on `ψ` is used.  @census none (helper) -/
theorem fPrimeBaseChange_natural (ψ : Species.Rep.Hom U V) (i j : Γ.VertexOrbit)
    (z : Balanced K (Γ.toSpecies.L j) L L
      (EtaleSpecies.Rep.tensor Γ.toSpecies i j (U.W i))) :
    fPrimeBaseChange V i j (hMapTensor ψ i j z)
      = Balanced.map (K := K) (A := Γ.toSpecies.L j) (Y := L)
          (U.smul_K_W j) (V.smul_K_W j) (ψ.ψ j) L (fPrimeBaseChange U i j z) := by
  have key : ((fPrimeBaseChange V i j).toAddMonoidHom.comp
        (hMapTensor ψ i j).toAddMonoidHom)
      = ((Balanced.map (K := K) (A := Γ.toSpecies.L j) (Y := L)
            (U.smul_K_W j) (V.smul_K_W j) (ψ.ψ j) L).toAddMonoidHom.comp
          (fPrimeBaseChange U i j).toAddMonoidHom) := by
    refine balanced_addHom_ext fun t a => ?_
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective
      (balancedRel K (Γ.toSpecies.L i) (Γ.toSpecies.L j) (Γ.toSpecies.M i j) (U.W i)) t
    induction s with
    | zero =>
        rw [show (Submodule.Quotient.mk (0 : Γ.toSpecies.M i j ⊗[K] U.W i) :
          EtaleSpecies.Rep.tensor Γ.toSpecies i j (U.W i)) = 0 from rfl,
          show Balanced.mk (K := K) (A := Γ.toSpecies.L j) (B := L)
            (0 : EtaleSpecies.Rep.tensor Γ.toSpecies i j (U.W i)) a = 0 from
            Balanced.mk_zero_left a]
        simp
    | tmul m w =>
        show fPrimeBaseChange V i j
            (hMapTensor ψ i j (Balanced.mk (Balanced.mk w m) a)) = _
        show fPrimeBaseChange V i j
            (Balanced.mk (Balanced.mk (ψ.ψ i w) m) a) = _
        show Balanced.mk (EtaleSpecies.Rep.f' Γ.toSpecies V i j
            (Balanced.mk (ψ.ψ i w) m)) a = _
        show _ = Balanced.mk (ψ.ψ j (EtaleSpecies.Rep.f' Γ.toSpecies U i j
            (Balanced.mk w m))) a
        exact congrArg
          (fun y : V.W j => Balanced.mk (K := K) (A := Γ.toSpecies.L j) (B := L) y a)
          (Species.Rep.Hom.comm_mk ψ i j w m)
    | add s t hs ht =>
        rw [show (Submodule.Quotient.mk (s + t) :
          EtaleSpecies.Rep.tensor Γ.toSpecies i j (U.W i))
            = Submodule.Quotient.mk s + Submodule.Quotient.mk t from rfl,
          Balanced.mk_add_left, map_add, map_add, hs, ht]
  exact DFunLike.congr_fun key z

open scoped Classical in
/-- **The composed identity**: `Ψ_j` intertwines the two `φ_e`-blocks, against the twisted
diagonal.  `phiEdgeBlock ∘ wiiMjL2Equiv` cancels on both sides, so this is `balancedKRat`'s
naturality composed with the species-morphism axiom.  @census none (helper) -/
theorem phiEdgeBlock_natural
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (ψ : Species.Rep.Hom U V) (i j : Γ.VertexOrbit)
    [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch i j ε))]
    (z : Balanced K (Γ.toSpecies.L j) L L
      (EtaleSpecies.Rep.tensor Γ.toSpecies i j (U.W i))) :
    hMapVertex WKU WKV hU hV ψ j
        (phiEdgeBlock U WKU hU ch i j (wiiMjL2Equiv U i j WKU hU ch z))
      = phiEdgeBlock V WKV hV ch i j
          (wiiMjL2Equiv V i j WKV hV ch (hMapTensor ψ i j z)) := by
  show hMapVertex WKU WKV hU hV ψ j (balancedKRat U WKU j (hU j)
      (fPrimeBaseChange U i j ((wiiMjL2Equiv U i j WKU hU ch).symm
        (wiiMjL2Equiv U i j WKU hU ch z)))) = _
  rw [LinearEquiv.symm_apply_apply]
  show _ = balancedKRat V WKV j (hV j) (fPrimeBaseChange V i j
      ((wiiMjL2Equiv V i j WKV hV ch).symm
        (wiiMjL2Equiv V i j WKV hV ch (hMapTensor ψ i j z))))
  rw [LinearEquiv.symm_apply_apply, fPrimeBaseChange_natural,
    balancedKRat_natural]

open scoped Classical in
/-- **`phiEdgeAt` on `kFormIncl`, at any coset** — the general form of `phiEdgeAt_kForm`, obtained
from `phiEdgeAt_wiiMjL2_general` at the constant tuple `m ≡ 1`.  @census none (helper) -/
theorem phiEdgeAt_kFormIncl {i j : Γ.VertexOrbit} (V : EtaleSpecies.Rep Γ.toSpecies)
    (WK : ∀ k : Γ.VertexOrbit, Submodule K (V.W k))
    (hWK : ∀ k : Γ.VertexOrbit, IsKRationalStructure V k (WK k))
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch i j ε)) (z : V.W i) :
    phiEdgeAt V WK hWK ch i j ε η
        (hPhi V WK (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹ * (ch i j ε).σ) i
          (kFormIncl V WK i (hWK i) z))
      = hPhi V WK (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹) j
          (phiEdgeRep V WK hWK ch i j ε
            (hPhi V WK (ch i j ε).σ i (kFormIncl V WK i (hWK i) z))) := by
  have hgen := phiEdgeAt_wiiMjL2_general V WK hWK ch ε η z (fun _ => 1)
  rw [wiiMjL2Equiv_apply, wiiMjL2Summand_kFormIncl V WK ε (ch i j ε)] at hgen
  simpa using hgen

open scoped Classical in
/-- **Per-summand naturality**: `Ψ_j` intertwines the two `(ε,η)`-components, against `Ψ^{ρ_η σ_ε}`
on the source.  @census none (helper) -/
theorem phiEdgeAt_natural
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (ψ : Species.Rep.Hom U V) {i j : Γ.VertexOrbit}
    (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch i j ε)) (y : hObj U WKU i) :
    hMapVertex WKU WKV hU hV ψ j (phiEdgeAt U WKU hU ch i j ε η y)
      = phiEdgeAt V WKV hV ch i j ε η
          (psiTwist WKU WKV hU hV ψ
            (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹ * (ch i j ε).σ) i y) := by
  set Y := DirectSum.lof L (Γ.EdgeOrbit i j)
      (fun ε => DirectSum (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj U WKU i)) ε
      (DirectSum.lof L (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj U WKU i) η y)
    with hYdef
  set z := (wiiMjL2Equiv U i j WKU hU ch).symm Y with hzdef
  have hz : wiiMjL2Equiv U i j WKU hU ch z = Y := LinearEquiv.apply_symm_apply _ _
  have hbal : wiiMjL2Equiv V i j WKV hV ch (hMapTensor ψ i j z)
      = DirectSum.lof L (Γ.EdgeOrbit i j)
          (fun ε => DirectSum (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj V WKV i)) ε
          (DirectSum.lof L (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj V WKV i) η
            (psiTwist WKU WKV hU hV ψ
              (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹ * (ch i j ε).σ) i y)) := by
    refine DFinsupp.ext fun ε' => ?_
    refine DFinsupp.ext fun η' => ?_
    rw [wiiMjL2Equiv_natural WKU WKV hU hV ch ψ i j ε' η' z, hz]
    rcases eq_or_ne ε' ε with rfl | hε
    · have h1 : Y ε' = DirectSum.lof L (EdgeChoice.CosetIndex Γ (ch i j ε'))
          (fun _ => hObj U WKU i) η y := by
        rw [hYdef, DirectSum.lof_eq_of, DirectSum.of_eq_same]
      have h1' : (DirectSum.lof L (Γ.EdgeOrbit i j)
            (fun ε => DirectSum (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj V WKV i)) ε'
            (DirectSum.lof L (EdgeChoice.CosetIndex Γ (ch i j ε')) (fun _ => hObj V WKV i) η
              (psiTwist WKU WKV hU hV ψ
                (EdgeChoice.rep Γ (ch i j ε') η * (ch i j ε').τ⁻¹ * (ch i j ε').σ) i y))) ε'
          = DirectSum.lof L (EdgeChoice.CosetIndex Γ (ch i j ε')) (fun _ => hObj V WKV i) η
              (psiTwist WKU WKV hU hV ψ
                (EdgeChoice.rep Γ (ch i j ε') η * (ch i j ε').τ⁻¹ * (ch i j ε').σ) i y) := by
        rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]
      rw [h1, h1']
      rcases eq_or_ne η' η with rfl | hη
      · rw [DirectSum.lof_eq_of, DirectSum.of_eq_same,
          DirectSum.lof_eq_of, DirectSum.of_eq_same]
      · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hη,
          DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hη, map_zero]
    · have h4 : Y ε' = 0 := by
        rw [hYdef, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hε]
      have h4' : (DirectSum.lof L (Γ.EdgeOrbit i j)
            (fun ε => DirectSum (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj V WKV i)) ε
            (DirectSum.lof L (EdgeChoice.CosetIndex Γ (ch i j ε)) (fun _ => hObj V WKV i) η
              (psiTwist WKU WKV hU hV ψ
                (EdgeChoice.rep Γ (ch i j ε) η * (ch i j ε).τ⁻¹ * (ch i j ε).σ) i y))) ε'
          = 0 := by
        rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hε]
      rw [h4, h4']
      have hz0 : ((0 : DirectSum (EdgeChoice.CosetIndex Γ (ch i j ε'))
          (fun _ => hObj U WKU i)) η') = 0 := rfl
      rw [hz0, map_zero]
      rfl
  have hkey := phiEdgeBlock_natural WKU WKV hU hV ch ψ i j z
  rw [hz, hbal] at hkey
  exact hkey

/-- `kFormIncl` on the coercion of a `K`-form element.  @census none (helper) -/
theorem kFormIncl_coe {i : Γ.VertexOrbit} (W : EtaleSpecies.Rep Γ.toSpecies)
    (WKW : ∀ k : Γ.VertexOrbit, Submodule K (W.W k))
    (h : IsKRationalStructure W i (WKW i)) (w : ↥(WKW i)) :
    kFormIncl W WKW i h ((w : W.W i)) = (1 : L) ⊗ₜ[K] w := by
  have h1 : (kRatEquiv W WKW h).symm ((w : W.W i)) = (1 : Γ.toSpecies.L i) ⊗ₜ[K] w := by
    refine (kRatEquiv W WKW h).injective ?_
    rw [LinearEquiv.apply_symm_apply]
    show _ = (1 : Γ.toSpecies.L i) • ((w : W.W i))
    rw [one_smul]
  show LinearMap.rTensor _ _ ((kRatEquiv W WKW h).symm ((w : W.W i))) = _
  rw [h1, LinearMap.rTensor_tmul]
  show (algebraMap (Γ.toSpecies.L i) L 1) ⊗ₜ[K] w = _
  rw [map_one]

open scoped Classical in
/-- **Clause `RQ2-1.09-C1` for `H.map`, at the orbit representative and on the `K`-form.**
@census none (helper) -/
theorem phiEdgeRep_natural_kForm
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (ψ : Species.Rep.Hom U V) {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (w : ↥(WKU i)) :
    psiTwist WKU WKV hU hV ψ (ch i j ε).τ j
        (phiEdgeRep U WKU hU ch i j ε ((1 : L) ⊗ₜ[K] w))
      = phiEdgeRep V WKV hV ch i j ε
          (psiTwist WKU WKV hU hV ψ (ch i j ε).σ i ((1 : L) ⊗ₜ[K] w)) := by
  have hfix : ∀ (g : Gal(L/K)) (W : EtaleSpecies.Rep Γ.toSpecies)
      (WKW : ∀ k : Γ.VertexOrbit, Submodule K (W.W k)) (x : ↥(WKW i)),
      hPhi W WKW g i ((1 : L) ⊗ₜ[K] x) = (1 : L) ⊗ₜ[K] x := by
    intro g W WKW x; rw [hPhi_tmul, map_one]
  have hsrcU : hPhi U WKU (ch i j ε).σ i (kFormIncl U WKU i (hU i) ((w : U.W i)))
      = (1 : L) ⊗ₜ[K] w := by rw [kFormIncl_coe, hfix]
  have hsrcV : hPhi V WKV (ch i j ε).σ i
      (kFormIncl V WKV i (hV i) (ψ.ψ i ((w : U.W i))))
      = psiTwist WKU WKV hU hV ψ (ch i j ε).σ i ((1 : L) ⊗ₜ[K] w) := by
    show _ = hPhi V WKV (ch i j ε).σ i (hMapVertex WKU WKV hU hV ψ i
      (hPhi U WKU (ch i j ε).σ⁻¹ i ((1 : L) ⊗ₜ[K] w)))
    rw [hfix, hMapVertex_kForm]
  have hnat := phiEdgeAt_natural WKU WKV hU hV ch ψ ε
    (EdgeChoice.cosetOne (ch i j ε))
    (hPhi U WKU (EdgeChoice.rep Γ (ch i j ε) (EdgeChoice.cosetOne (ch i j ε))
        * (ch i j ε).τ⁻¹ * (ch i j ε).σ) i
      (kFormIncl U WKU i (hU i) ((w : U.W i))))
  rw [phiEdgeAt_kFormIncl U WKU hU ch ε (EdgeChoice.cosetOne (ch i j ε)) ((w : U.W i)),
    psiTwist_hPhi,
    phiEdgeAt_kFormIncl V WKV hV ch ε (EdgeChoice.cosetOne (ch i j ε))
      (ψ.ψ i ((w : U.W i))),
    hsrcU, hsrcV] at hnat
  have hcong : (EdgeChoice.rep Γ (ch i j ε) (EdgeChoice.cosetOne (ch i j ε))
      * (ch i j ε).τ⁻¹)⁻¹ • Γ.vertexRep j = (ch i j ε).τ • Γ.vertexRep j := by
    rw [mul_inv_rev, inv_inv, mul_smul,
      show (EdgeChoice.rep Γ (ch i j ε) (EdgeChoice.cosetOne (ch i j ε)))⁻¹
          • Γ.vertexRep j = Γ.vertexRep j from
        mem_stabilizer_iff.mp (inv_mem
          (mem_stabilizer_iff.mpr ((ch i j ε).rep_mem (EdgeChoice.cosetOne (ch i j ε)))))]
  rw [← psiTwist_congr WKU WKV hU hV ψ j
    (EdgeChoice.rep Γ (ch i j ε) (EdgeChoice.cosetOne (ch i j ε)) * (ch i j ε).τ⁻¹)⁻¹
    (ch i j ε).τ hcong]
  show hPhi V WKV _ j (hMapVertex WKU WKV hU hV ψ j
    (hPhi U WKU (EdgeChoice.rep Γ (ch i j ε) (EdgeChoice.cosetOne (ch i j ε))
      * (ch i j ε).τ⁻¹)⁻¹⁻¹ j
      (phiEdgeRep U WKU hU ch i j ε ((1 : L) ⊗ₜ[K] w)))) = _
  rw [inv_inv, hnat, hPhi_comp, inv_mul_cancel, hPhi_one]

/-- `psiTwist` absorbs a left translation.  @census none (helper) -/
theorem psiTwist_mul_hPhi (ψ : Species.Rep.Hom U V) (k : Γ.VertexOrbit) (g h : Gal(L/K))
    (y : hObj U WKU k) :
    psiTwist WKU WKV hU hV ψ (h * g) k (hPhi U WKU h k y)
      = hPhi V WKV h k (psiTwist WKU WKV hU hV ψ g k y) := by
  show hPhi V WKV (h * g) k (hMapVertex WKU WKV hU hV ψ k
      (hPhi U WKU (h * g)⁻¹ k (hPhi U WKU h k y)))
    = hPhi V WKV h k (hPhi V WKV g k (hMapVertex WKU WKV hU hV ψ k
        (hPhi U WKU g⁻¹ k y)))
  rw [hPhi_comp, show (h * g)⁻¹ * h = g⁻¹ from by group, hPhi_comp]

open scoped Classical in
/-- **The edge axiom at the representative, for every argument** — `phiEdgeRep` is
`liftBaseChange`, so `L`-linearity carries §62.19 off the `K`-form.  @census none (helper) -/
theorem phiEdgeRep_natural
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (ψ : Species.Rep.Hom U V) {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (X : hObj U WKU i) :
    psiTwist WKU WKV hU hV ψ (ch i j ε).τ j (phiEdgeRep U WKU hU ch i j ε X)
      = phiEdgeRep V WKV hV ch i j ε
          (psiTwist WKU WKV hU hV ψ (ch i j ε).σ i X) := by
  induction X using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a w =>
      rw [show (a ⊗ₜ[K] w : hObj U WKU i) = a • ((1 : L) ⊗ₜ[K] w) from by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul,
        phiEdgeRep_natural_kForm]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

open scoped Classical in
/-- **The edge axiom at every edge.**  The translation `g_e` carrying `e_ε` to `e` moves `σ_ε` and
`τ_ε` to translations for `s(e)` and `t(e)`, and `psiTwist_congr` recognises the vertex family
there.  @census none (helper) -/
theorem phiEdgeAtIdx_natural
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (ψ : Species.Rep.Hom U V) {i j : Γ.VertexOrbit} (e : Γ.E)
    (hs : Γ.vertexClass (Γ.toRQuiver.source e) = i)
    (ht : Γ.vertexClass (Γ.toRQuiver.target e) = j) (X : hObj U WKU i) :
    psiTwist WKU WKV hU hV ψ
        (edgeTrans i j e hs ht * (ch i j (edgeClassAt i j e hs ht)).τ) j
        (phiEdgeAtIdx U WKU hU ch i j e hs ht X)
      = phiEdgeAtIdx V WKV hV ch i j e hs ht
          (psiTwist WKU WKV hU hV ψ
            (edgeTrans i j e hs ht * (ch i j (edgeClassAt i j e hs ht)).σ) i X) := by
  show psiTwist WKU WKV hU hV ψ _ j
      (hPhi U WKU (edgeTrans i j e hs ht) j
        (phiEdgeRep U WKU hU ch i j (edgeClassAt i j e hs ht)
          (hPhi U WKU (edgeTrans i j e hs ht)⁻¹ i X))) = _
  rw [psiTwist_mul_hPhi, phiEdgeRep_natural]
  show _ = hPhi V WKV (edgeTrans i j e hs ht) j
      (phiEdgeRep V WKV hV ch i j (edgeClassAt i j e hs ht)
        (hPhi V WKV (edgeTrans i j e hs ht)⁻¹ i
          (psiTwist WKU WKV hU hV ψ _ i X)))
  congr 2
  rw [← psiTwist_mul_hPhi WKU WKV hU hV ψ i
      (edgeTrans i j e hs ht * (ch i j (edgeClassAt i j e hs ht)).σ)
      (edgeTrans i j e hs ht)⁻¹ X, inv_mul_cancel_left]

/-- `hMapPsi` unfolded — a `rfl` pin, so proofs rewrite rather than `show`.  @census none -/
theorem hMapPsi_eq (ψ : Species.Rep.Hom U V) (v : Γ.V) :
    hMapPsi WKU WKV hU hV ψ v
      = psiTwist WKU WKV hU hV ψ (vertexTrans v) (Γ.vertexClass v) := rfl

/-- `hObjCast` cancels its own inverse, the other way.  @census none (helper) -/
@[simp] theorem hObjCast_cast_symm {W : EtaleSpecies.Rep Γ.toSpecies}
    {WKW : ∀ k : Γ.VertexOrbit, Submodule K (W.W k)}
    {i i' : Γ.VertexOrbit} (h : i = i') (x : hObj W WKW i) :
    hObjCast W WKW h.symm (hObjCast W WKW h x) = x := by subst h; rfl

open scoped Classical in
/-- **Clause `RQ2-1.09-C1` for `H.map`** — the `edge` field, at a fixed pair of vertex orbits so the
terms stay small.  `psiTwist_congr` recognises the vertex family at the two translations the edge
supplies, and `phiEdgeAtIdx_natural` does the rest.  @census none (helper) -/
theorem hMapPsi_edge_at
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (ψ : Species.Rep.Hom U V) {i j : Γ.VertexOrbit} (e : Γ.E)
    (hs : Γ.vertexClass (Γ.toRQuiver.source e) = i)
    (ht : Γ.vertexClass (Γ.toRQuiver.target e) = j)
    (m : hObj U WKU i) :
    psiTwist WKU WKV hU hV ψ (vertexTrans (Γ.toRQuiver.target e)) j
        (phiEdgeAtIdx U WKU hU ch i j e hs ht m)
      = phiEdgeAtIdx V WKV hV ch i j e hs ht
          (psiTwist WKU WKV hU hV ψ (vertexTrans (Γ.toRQuiver.source e)) i m) := by
  have hT1 : (edgeTrans i j e hs ht * (ch i j (edgeClassAt i j e hs ht)).τ)
      • Γ.vertexRep j = Γ.toRQuiver.target e := by
    rw [mul_smul, EdgeChoice.target_eq, ← Γ.target_smul, edgeTrans_spec]
  have hT2 : vertexTrans (Γ.toRQuiver.target e) • Γ.vertexRep j
      = Γ.toRQuiver.target e := by
    rw [← ht]; exact vertexTrans_spec _
  have hS1 : (edgeTrans i j e hs ht * (ch i j (edgeClassAt i j e hs ht)).σ)
      • Γ.vertexRep i = Γ.toRQuiver.source e := by
    rw [mul_smul, EdgeChoice.source_eq, ← Γ.source_smul, edgeTrans_spec]
  have hS2 : vertexTrans (Γ.toRQuiver.source e) • Γ.vertexRep i
      = Γ.toRQuiver.source e := by
    rw [← hs]; exact vertexTrans_spec _
  refine Eq.trans
    (psiTwist_congr WKU WKV hU hV ψ j _ _ (hT1.trans hT2.symm) _).symm ?_
  refine Eq.trans (phiEdgeAtIdx_natural WKU WKV hU hV ch ψ e hs ht m) ?_
  exact congrArg _ (psiTwist_congr WKU WKV hU hV ψ i _ _ (hS1.trans hS2.symm) m)

open scoped Classical in
/-- The `edge` field, stated in the shape `Rep.Hom` asks for.  @census none (helper) -/
theorem hMapPsi_edge
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (ψ : Species.Rep.Hom U V) (e : Γ.E)
    (m : hObj U WKU (Γ.vertexClass (Γ.toRQuiver.source e))) :
    hMapPsi WKU WKV hU hV ψ (Γ.toRQuiver.target e)
        ((hObjRep U WKU hU ch).toRep.φEdge e m)
      = (hObjRep V WKV hV ch).toRep.φEdge e
          (hMapPsi WKU WKV hU hV ψ (Γ.toRQuiver.source e) m) := by
  have h := hMapPsi_edge_at WKU WKV hU hV ch ψ e
    (rfl : Γ.vertexClass (Γ.toRQuiver.source e) = Γ.vertexClass (Γ.toRQuiver.source e))
    (rfl : Γ.vertexClass (Γ.toRQuiver.target e) = Γ.vertexClass (Γ.toRQuiver.target e)) m
  rw [hObjRep_phiEdge, hObjRep_phiEdge, phiEdgeFull_eq, phiEdgeFull_eq]
  exact h

open scoped Classical in
/-- **`H` on morphisms**, as a morphism of `Rep(Γ_K)`.  Both fields are proved: `rational` by the
group law (§62.18) and `edge` by §62.19 transported to every edge.
@census none (clause witness for `RQ2-2.28-C5`) -/
noncomputable def hMapHom
    (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)
    (ψ : Species.Rep.Hom U V) :
    Rep.Hom (hObjRep U WKU hU ch).toRep (hObjRep V WKV hV ch).toRep where
  ψ v := hMapPsi WKU WKV hU hV ψ v
  rational σ v m := by
    have h := hMapPsi_rational WKU WKV hU hV ψ σ v m
    have h2 := congrArg (hObjCast V WKV (vertexClass_smul σ v).symm) h
    rw [hObjCast_cast_symm] at h2
    exact h2
  edge e m := hMapPsi_edge WKU WKV hU hV ch ψ e m

/-- **The computation `RQ2-2.29`'s hypothesis `hH3` runs on** (finding `S5-F9`): at the orbit
**representative** `v_i`, `H.map ψ` carries `e_fix`'s forward map for `U` to `e_fix`'s forward map
for `V`, composed with `ψ_i`.

`hMapPsi` at `v` is `psiTwist` twisted by `vertexTrans v`; at `v = v_i` that element **fixes**
`v_i`, so `hPhi_fix_kFormIncl` makes the twist wash out on `kFormIncl`'s image — the `Exists.choose`
in `vertexTrans` washing out exactly where `phiEdgeAtIdx_edgeRep` makes the one in `edgeTrans` wash
out on the edge side (§62.20).  What is left is `hMapVertex_kFormIncl`, "on a `K`-form generator the
base change is `kFormIncl` of `ψ`'s value".

@census none (clause witness for `RQ2-2.28-C5`; the engine of `hFunctor_hH3`) -/
theorem hMapPsi_kFormIncl
    (ψ : Species.Rep.Hom U V) (i : Γ.VertexOrbit) (w : U.W i) :
    hMapPsi WKU WKV hU hV ψ (Γ.vertexRep i)
        (hObjCast U WKU (Γ.vertexClass_vertexRep i).symm (kFormIncl U WKU i (hU i) w))
      = hObjCast V WKV (Γ.vertexClass_vertexRep i).symm
          (kFormIncl V WKV i (hV i) (ψ.ψ i w)) := by
  have hg : vertexTrans (Γ.vertexRep i) • Γ.vertexRep i = Γ.vertexRep i := by
    have h := vertexTrans_spec (Γ.vertexRep i)
    rwa [Γ.vertexClass_vertexRep i] at h
  have hcore : psiTwist WKU WKV hU hV ψ (vertexTrans (Γ.vertexRep i)) i
        (kFormIncl U WKU i (hU i) w)
      = kFormIncl V WKV i (hV i) (ψ.ψ i w) := by
    rw [← hPhi_fix_kFormIncl U WKU i (hU i) (vertexTrans (Γ.vertexRep i)) hg w,
      psiTwist_hPhi WKU WKV hU hV ψ (vertexTrans (Γ.vertexRep i)) i w,
      hPhi_fix_kFormIncl V WKV i (hV i) (vertexTrans (Γ.vertexRep i)) hg]
  show psiTwist WKU WKV hU hV ψ (vertexTrans (Γ.vertexRep i))
      (Γ.vertexClass (Γ.vertexRep i))
      (hObjCast U WKU (Γ.vertexClass_vertexRep i).symm (kFormIncl U WKU i (hU i) w)) = _
  rw [← psiTwist_hObjCast WKU WKV hU hV ψ (vertexTrans (Γ.vertexRep i))
    (Γ.vertexClass_vertexRep i).symm, hcore]

/-- `hMapVertex` of the identity is the identity.  @census none (helper) -/
theorem hMapVertex_id (i : Γ.VertexOrbit) (y : hObj U WKU i) :
    hMapVertex WKU WKU hU hU (Species.Rep.Hom.id U) i y = y := by
  show hObjEquivBaseChange U WKU i (hU i) (psiBase (Species.Rep.Hom.id U) i
    ((hObjEquivBaseChange U WKU i (hU i)).symm y)) = _
  have hb : ∀ t : L ⊗[Γ.toSpecies.L i] (U.W i),
      psiBase (Species.Rep.Hom.id U) i t = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul a z => rfl
    | add p q hp hq => rw [map_add, hp, hq]
  rw [hb, LinearEquiv.apply_symm_apply]

/-- `hMapVertex` of a composite is the composite.  @census none (helper) -/
theorem hMapVertex_comp {W : EtaleSpecies.Rep Γ.toSpecies}
    (WKW : ∀ i : Γ.VertexOrbit, Submodule K (W.W i))
    (hW : ∀ k : Γ.VertexOrbit, IsKRationalStructure W k (WKW k))
    (ψ : Species.Rep.Hom U V) (χ : Species.Rep.Hom V W) (i : Γ.VertexOrbit)
    (y : hObj U WKU i) :
    hMapVertex WKU WKW hU hW (ψ.comp χ) i y
      = hMapVertex WKV WKW hV hW χ i (hMapVertex WKU WKV hU hV ψ i y) := by
  show hObjEquivBaseChange W WKW i (hW i) (psiBase (ψ.comp χ) i
    ((hObjEquivBaseChange U WKU i (hU i)).symm y)) = _
  show _ = hObjEquivBaseChange W WKW i (hW i) (psiBase χ i
    ((hObjEquivBaseChange V WKV i (hV i)).symm
      (hObjEquivBaseChange V WKV i (hV i) (psiBase ψ i
        ((hObjEquivBaseChange U WKU i (hU i)).symm y)))))
  rw [LinearEquiv.symm_apply_apply]
  congr 1
  generalize (hObjEquivBaseChange U WKU i (hU i)).symm y = t
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a z => rfl
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]

end HMapPsi

section HFunctor
variable (WK : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit), Submodule K (V.W i))
  (hWK : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit),
    IsKRationalStructure V i (WK V i))
  (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)

/-- `hMapPsi` of the identity is the identity.  @census none (helper) -/
theorem hMapPsi_id (V : EtaleSpecies.Rep Γ.toSpecies) (v : Γ.V)
    (y : hObj V (WK V) (Γ.vertexClass v)) :
    hMapPsi (WK V) (WK V) (hWK V) (hWK V) (Species.Rep.Hom.id V) v y = y := by
  show hPhi V (WK V) (vertexTrans v) (Γ.vertexClass v)
      (hMapVertex (WK V) (WK V) (hWK V) (hWK V) (Species.Rep.Hom.id V) (Γ.vertexClass v)
        (hPhi V (WK V) (vertexTrans v)⁻¹ (Γ.vertexClass v) y)) = y
  rw [hMapVertex_id, hPhi_comp, mul_inv_cancel, hPhi_one]

/-- `hMapPsi` of a composite is the composite.  @census none (helper) -/
theorem hMapPsi_comp {U V W : EtaleSpecies.Rep Γ.toSpecies}
    (ψ : Species.Rep.Hom U V) (χ : Species.Rep.Hom V W) (v : Γ.V)
    (y : hObj U (WK U) (Γ.vertexClass v)) :
    hMapPsi (WK U) (WK W) (hWK U) (hWK W) (ψ.comp χ) v y
      = hMapPsi (WK V) (WK W) (hWK V) (hWK W) χ v
          (hMapPsi (WK U) (WK V) (hWK U) (hWK V) ψ v y) := by
  show hPhi W (WK W) (vertexTrans v) (Γ.vertexClass v)
      (hMapVertex (WK U) (WK W) (hWK U) (hWK W) (ψ.comp χ) (Γ.vertexClass v)
        (hPhi U (WK U) (vertexTrans v)⁻¹ (Γ.vertexClass v) y)) = _
  show _ = hPhi W (WK W) (vertexTrans v) (Γ.vertexClass v)
      (hMapVertex (WK V) (WK W) (hWK V) (hWK W) χ (Γ.vertexClass v)
        (hPhi V (WK V) (vertexTrans v)⁻¹ (Γ.vertexClass v)
          (hPhi V (WK V) (vertexTrans v) (Γ.vertexClass v)
            (hMapVertex (WK U) (WK V) (hWK U) (hWK V) ψ (Γ.vertexClass v)
              (hPhi U (WK U) (vertexTrans v)⁻¹ (Γ.vertexClass v) y)))))
  rw [hPhi_comp, inv_mul_cancel, hPhi_one,
    hMapVertex_comp (WK U) (WK V) (hWK U) (hWK V) (WK W) (hWK W) ψ χ]

open scoped Classical in
/-- **The functor `H : Rep(S(Γ_K)) → Rep(Γ_K)`** (clause `RQ2-2.28-C5`). -/
noncomputable def hFunctor :
    CategoryTheory.Functor (EtaleSpecies.Rep Γ.toSpecies) (FDRep Γ) where
  obj V := hObjRep V (WK V) (hWK V) ch
  map {U V} ψ := hMapHom (WK U) (WK V) (hWK U) (hWK V) ch ψ
  map_id V := by
    refine Rep.Hom.ext ?_
    funext v
    refine LinearMap.ext fun y => ?_
    exact hMapPsi_id WK hWK V v y
  map_comp {U V W} ψ χ := by
    refine Rep.Hom.ext ?_
    funext v
    refine LinearMap.ext fun y => ?_
    exact hMapPsi_comp WK hWK ψ χ v y

/-- `hFunctor`'s object map — a `rfl` pin, per §62.20.  @census none (helper) -/
theorem hFunctor_obj (V : EtaleSpecies.Rep Γ.toSpecies) :
    (hFunctor WK hWK ch).obj V = hObjRep V (WK V) (hWK V) ch := rfl

open scoped Classical in
/-- **`RQ2-2.29`'s hypothesis `hH3`, discharged for this project's own `H`** — the finding `S5-F9`
binder, verified non-vacuous by a compiled proof rather than by prose.

`hH3` says: for `ψ : V ⟶ V'` and any family `ψ'` agreeing with `H.map ψ` on the
`G_{v_i}`-invariants, `ψ'` is `ψ_i` under the descent identification `e_fix`.  The proof is
`hMapPsi_kFormIncl` read through `eFix_symm_apply`: `e_fix`'s inverse **is** `eFixFwd`, whose value
is `hObjCast ∘ kFormIncl`, which is precisely where `hMapPsi_kFormIncl` computes `H.map ψ`.

This is the declaration the G4 verifier's finding `V-S5G4-3`(c) asked for on the `hH3` side: the
docstring of `species_equivalence` previously named `hMapHom` — a `def`, the morphism map itself —
as the witness that `hH3` is satisfiable, which it is not.

@census none (clause witness for `RQ2-2.28-C5`; discharges `RQ2-2.29`'s `hH3`) -/
theorem hFunctor_hH3 (V V' : EtaleSpecies.Rep Γ.toSpecies) (ψ : V ⟶ V')
    (ψ' : ∀ i : Γ.VertexOrbit,
      ↥(((hFunctor WK hWK ch).obj V).toRep.vertexFixed (Γ.vertexRep i))
        →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ]
          ↥(((hFunctor WK hWK ch).obj V').toRep.vertexFixed (Γ.vertexRep i)))
    (hψ' : ∀ (i : Γ.VertexOrbit)
        (u : ↥(((hFunctor WK hWK ch).obj V).toRep.vertexFixed (Γ.vertexRep i))),
      ((ψ' i u : ((hFunctor WK hWK ch).obj V').toRep.M (Γ.vertexRep i)))
        = ((hFunctor WK hWK ch).map ψ).ψ (Γ.vertexRep i)
            (u : ((hFunctor WK hWK ch).obj V).toRep.M (Γ.vertexRep i)))
    (i : Γ.VertexOrbit)
    (u : ↥(((hFunctor WK hWK ch).obj V).toRep.vertexFixed (Γ.vertexRep i))) :
    eFix V' (WK V') (hWK V') ch i (ψ' i u)
      = ψ.ψ i (eFix V (WK V) (hWK V) ch i u) := by
  obtain ⟨w, rfl⟩ : ∃ w : V.W i, eFixFwd V (WK V) (hWK V) ch i w = u :=
    ⟨eFix V (WK V) (hWK V) ch i u, by
      rw [← eFix_symm_apply V (WK V) (hWK V) ch i, LinearEquiv.symm_apply_apply]⟩
  have hfix : eFix V (WK V) (hWK V) ch i (eFixFwd V (WK V) (hWK V) ch i w) = w := by
    rw [← eFix_symm_apply V (WK V) (hWK V) ch i, LinearEquiv.apply_symm_apply]
  have key : ψ' i (eFixFwd V (WK V) (hWK V) ch i w)
      = (eFix V' (WK V') (hWK V') ch i).symm (ψ.ψ i w) := by
    rw [eFix_symm_apply]
    refine Subtype.ext ?_
    rw [hψ' i (eFixFwd V (WK V) (hWK V) ch i w)]
    exact hMapPsi_kFormIncl (WK V) (WK V') (hWK V) (hWK V') ψ i w
  rw [hfix, key, LinearEquiv.apply_symm_apply]

open scoped Classical in
/-- **Clause `RQ2-2.28-C3`**: the displayed square.  With `e_obj` the identity, `φ_{v,η}` is `η` on
the `L` factor alone — which is `hPhi` on the nose.  @census none (clause witness) -/
theorem hObjRep_phi'_tmul (V : EtaleSpecies.Rep Γ.toSpecies) (v : Γ.V) (η : Gal(L/K))
    (hη : η • v = v) (a : L) (w : ↥(WK V (Γ.vertexClass v))) :
    (hObjRep V (WK V) (hWK V) ch).toRep.φ' η hη (a ⊗ₜ[K] w) = (η a) ⊗ₜ[K] w := by
  rw [hObjRep_phi'_apply, hPhi_tmul]

end HFunctor



/-! ### `RQ2-2.28-C2` — the cocycle lands in `G_{v_j}`  (G4)

`η_{e,σ} := τ_{ε(σe)}⁻¹ σ_{σe}⁻¹ σ σ_e τ_{ε(e)}` is the source's cocycle, and the clause is that it
stabilises `v_j`.  Pure bookkeeping, and it is the §2.6 preamble's two equations doing exactly what
they were chosen for: `τ_ε` carries `v_j` to `t(e_ε)`, the three group elements then walk that
target along the edge orbit by `target_smul`, and `τ_{ε'}⁻¹` carries it back.

@census none (clause witness for `RQ2-2.28-C2`)
@clauses   RQ2-2.28-C2
-/

/-- **Clause `RQ2-2.28-C2`**: the cocycle `η_{e,σ} = τ_{ε(σe)}⁻¹ σ_{σe}⁻¹ σ σ_e τ_{ε(e)}` lies in
`G_{v_j}`. -/
theorem cocycle_mem_stabilizer
    (ch : ∀ (i j : Γ.VertexOrbit) (ε : Γ.EdgeOrbit i j), Γ.EdgeChoice ε)
    (i j : Γ.VertexOrbit) (ε ε' : Γ.EdgeOrbit i j) (σ σe σse : Gal(L/K))
    (hσe : σe • Γ.edgeRep ε = Γ.edgeRep ε)
    (hσse : σse • Γ.edgeRep ε' = σ • Γ.edgeRep ε) :
    ((ch i j ε').τ⁻¹ * σse⁻¹ * σ * σe * (ch i j ε).τ) • Γ.vertexRep j = Γ.vertexRep j := by
  have h1 : (ch i j ε).τ • Γ.vertexRep j = Γ.toRQuiver.target (Γ.edgeRep ε) :=
    (ch i j ε).target_eq
  have h2 : (ch i j ε').τ • Γ.vertexRep j = Γ.toRQuiver.target (Γ.edgeRep ε') :=
    (ch i j ε').target_eq
  have hedge : (σse⁻¹ * σ) • Γ.edgeRep ε = Γ.edgeRep ε' := by
    rw [mul_smul, ← hσse, inv_smul_smul]
  calc ((ch i j ε').τ⁻¹ * σse⁻¹ * σ * σe * (ch i j ε).τ) • Γ.vertexRep j
      = (ch i j ε').τ⁻¹ • ((σse⁻¹ * σ) • (σe • ((ch i j ε).τ • Γ.vertexRep j))) := by
        simp only [mul_smul]
    _ = (ch i j ε').τ⁻¹ • ((σse⁻¹ * σ) • (σe • Γ.toRQuiver.target (Γ.edgeRep ε))) := by
        rw [h1]
    _ = (ch i j ε').τ⁻¹ • ((σse⁻¹ * σ) • Γ.toRQuiver.target (Γ.edgeRep ε)) := by
        rw [← Γ.target_smul, hσe]
    _ = (ch i j ε').τ⁻¹ • Γ.toRQuiver.target (Γ.edgeRep ε') := by
        rw [← Γ.target_smul, hedge]
    _ = Γ.vertexRep j := by rw [← h2, inv_smul_smul]

/-- **Proposition** (`unlabeled:6`, census `RQ2-2.28`).

For all `σ ∈ G` and all `e ∈ E` (clause `RQ2-2.28-H1`), with `φ_e` the displayed composition through
`eq:WiiMjL2` and `f_{ij} ⊗ 1_L`, and `σ_e ∈ G` chosen with `σ_e e_{ε(e)} = e` (clause
`RQ2-2.28-H2`):

* `φ_e` is `L`-**linear** (clause `RQ2-2.28-C1`) — the `φEdge` field of `H.obj V`;
* `η_{e,σ} := τ_{ε(σe)}^{-1} σ_{σe}^{-1} σ σ_e τ_{ε(e)}` lies in `G_{v_j}` (clause `RQ2-2.28-C2`);
* the displayed squares **commute** (clause `RQ2-2.28-C3`);
* `φ_e` satisfies `eq:koecheractiononrep` (clause `RQ2-2.28-C4`) — the `edge_equivariance` field;
* and `H` is a **functor** (clause `RQ2-2.28-C5`).

@census    RQ2-2.28
@source    prop:hcocycle
@clauses   RQ2-2.28-H1, RQ2-2.28-H2, RQ2-2.28-C1, RQ2-2.28-C2, RQ2-2.28-C3, RQ2-2.28-C4, RQ2-2.28-C5
@imports   none
@divergence JUSTIFIED_REFORMULATION on clauses `RQ2-2.28-H2`, `RQ2-2.28-C1`, `RQ2-2.28-C4`;
WEAKENED_OR_PARTIAL on clause `RQ2-2.28-C5` and on the statement's last sentence (independence of
the `K`-structures), since census r18. Until 2026-10-03 `C5` was listed as a reformulation; see the
dated `C5` paragraph below.

`H2` has two halves.  Half (b) — `σ_e` with `σ_e e_{ε(e)} = e` — is the local binder `σe` of the
`C2` conjunct, whose hypothesis `σe • edgeRep ε = edgeRep ε` is exactly that condition.  Half (a) —
`φ_e` *is* the displayed composite — is the third conjunct, and it is stated the way `RQ2-2.26-C1`
states its mirror: by pinning the **descent** of `H.obj V`'s edge maps, for any `IsEdgeDescent`
witness, to be `V`'s own structure map `f_{ij}` read through the identification `e_fix`.  That is
the same composite the source displays, written from the other end; writing the composite literally
would require naming `eq:WiiMjL2`'s isomorphism *and* the edge-to-`(ε,η)` correspondence inside the
statement, and the descent formulation determines `φ_e` just as tightly with the ingredients the
stage already has.

`C1` and `C4` are discharged by the type of `H.obj V`, as the section note above explains — and,
after the `H2`(a) repair, non-vacuously.  `C3` is the displayed square in the form
`1 ⊗ 1 ⊗ η_{e,σ}`: the translation by an element `η` fixing a vertex acts on `M(v) = L ⊗_K W_{v,K}`
through `η` on the `L` factor alone.  It is stated for a general `η` fixing a general vertex rather
than only for the `η_{e,σ}` of `C2`, which is *stronger* and avoids re-deriving the cocycle's index
bookkeeping inside the clause.

`C5` — "H is a functor" is the existential `∃ H : Rep(S(Γ_K)) ⥤ Rep(Γ_K)` with its object map
pinned by `e_obj` against `RQ2-2.27`, in the same shape as `RQ2-2.26`. **Partial, disclosed
2026-10-03** (docstring-only `R-PROC-4` amendment of frozen S5, coordinator ruling `R-FR-9`,
final-release WP-16b, `MISMATCH-TRIAGE.md` rows #5/#6). Census r18 re-synced `C5` and the
statement's conclusion. `C5` now says that, for `v = σ v_i`, `M(v) = W_i ⊗_{L_i,σ} L` canonically
(independent of `σ` modulo `G_{v_i}`, with `φ_{v,τ}` becoming `w ⊗ a ↦ w ⊗ τ a`), and that `H` sends
a morphism `(ψ_i)_i` to `ψ_i ⊗ 1_L`. The conclusion adds that different choices of the
`W_{i,K}` give naturally isomorphic functors. This theorem's `H.map` is **unconstrained**: only
`map_id`/`map_comp` hold, by functoriality. The earlier wording "object map pinned" is true, but it
is not the r18 clause. The faithful witnesses, for the concrete `hFunctor`, are
`RationalQuiver.hFunctor_map_formula` (the identification `hIdent`, its `σ`-semilinearity and
independence of `σ` modulo `G_{v_i}`, `φ_{v,τ}(a ⊗ w) = τa ⊗ w`, and `H ψ = ψ_i ⊗ 1_L`) and
`RationalQuiver.hFunctor_indep_KStructure` (any two choices `WK`, `WK'` give isomorphic functors),
both in `Species/Rep/ReleaseAddenda.lean` (final-release WP-16a). This theorem stays the row's
claimant. It is the only declaration that states `C2` and `H2`(a), and `rqaudit` admits one
claimant per row; the WP-16a theorems are clause witnesses (`@census none`).

The choice of `K`-rational structures is the argument `WK`, a function of the **object** — `H` is a
functor only once the choice is made for every object, which is the sense in which the census note
says `H` depends on the choice up to natural isomorphism — and it now carries its defining property
`hWK` (`IsKRationalStructure`, finding **V-S5b-2**); without it `WK V i := ⊥` refuted the row.

Proof plan (G4): `C2` is the source's own four-line computation; `H2`(a) and `C3` are the two
displayed squares; `C5`'s morphism map is base change of the `ψ_i` along `− ⊗_K L`, functorial
because base change is.
-/
theorem H_cocycle
    (WK : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit), Submodule K (V.W i))
    (hWK : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit),
      IsKRationalStructure V i (WK V i))
    (ch : ∀ (i j : Γ.VertexOrbit) (ε : Γ.EdgeOrbit i j), Γ.EdgeChoice ε) :
    -- `C2`: `η_{e,σ} := τ_{ε(σe)}⁻¹ σ_{σe}⁻¹ σ σ_e τ_{ε(e)}` lies in `G_{v_j}`
    (∀ (i j : Γ.VertexOrbit) (ε ε' : Γ.EdgeOrbit i j) (σ σe σse : Gal(L/K)),
      σe • Γ.edgeRep ε = Γ.edgeRep ε → σse • Γ.edgeRep ε' = σ • Γ.edgeRep ε →
      ((ch i j ε').τ⁻¹ * σse⁻¹ * σ * σe * (ch i j ε).τ) • Γ.vertexRep j = Γ.vertexRep j) ∧
    ∃ (H : CategoryTheory.Functor (EtaleSpecies.Rep Γ.toSpecies) (FDRep Γ))
      (e_obj : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (v : Γ.V),
        (H.obj V).toRep.M v ≃ₗ[L] hObj V (WK V) (Γ.vertexClass v))
      (e_fix : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit),
        ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
          ≃ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] V.W i),
      -- `H2`(a) + `C1` + `C4`: `φ_e` is the displayed composite through `eq:WiiMjL2` and
      -- `f_{ij} ⊗ 1_L` — stated, as `RQ2-2.26-C1` states its mirror, by pinning the **descent**
      -- of `H.obj V`'s edge maps to be `V`'s own structure map.
      (∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i j : Γ.VertexOrbit)
          (chij : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
          (e₀ : wiiMjL (H.obj V).toRep i j ≃ₗ[L] wiiMjLpreRhs (H.obj V).toRep chij)
          (fH : EtaleSpecies.Rep.tensor Γ.toSpecies i j
                  ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
                →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep j))),
        IsEdgeDescent (H.obj V).toRep chij e₀ fH →
        ∀ (w : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j),
          e_fix V j (fH (Balanced.mk w m))
            = EtaleSpecies.Rep.f' Γ.toSpecies V i j (Balanced.mk (e_fix V i w) m)) ∧
      -- `C3`: the displayed square — the translation by `η_{e,σ}` on `M(v_j)` is
      -- `1 ⊗ 1 ⊗ η_{e,σ}` on `W_i ⊗_{L_i} {}_iM_j ⊗_{L_j} L`, i.e. `η` acting on the `L` factor.
      (∀ (V : EtaleSpecies.Rep Γ.toSpecies) (v : Γ.V) (η : Gal(L/K)) (hη : η • v = v)
          (a : L) (w : ↥(WK V (Γ.vertexClass v))),
        e_obj V v ((H.obj V).toRep.φ' η hη ((e_obj V v).symm (a ⊗ₜ w)))
          = η a ⊗ₜ w) ∧
      -- `C5`: `H` is a functor
      ((∀ V : EtaleSpecies.Rep Γ.toSpecies, H.map (𝟙 V) = 𝟙 (H.obj V)) ∧
        ∀ (U V W : EtaleSpecies.Rep Γ.toSpecies) (φ : U ⟶ V) (χ : V ⟶ W),
          H.map (φ ≫ χ) = H.map φ ≫ H.map χ) := by
  classical
  refine ⟨fun i j ε ε' σ σe σse hσe hσse =>
      cocycle_mem_stabilizer ch i j ε ε' σ σe σse hσe hσse, ?_⟩
  refine ⟨hFunctor WK hWK ch,
    fun V v => LinearEquiv.refl L (hObj V (WK V) (Γ.vertexClass v)),
    fun V i => eFix V (WK V) (hWK V) ch i,
    ?_, ?_, (hFunctor WK hWK ch).map_id,
    fun U V W φ χ => (hFunctor WK hWK ch).map_comp φ χ⟩
  · exact fun V i j chij e₀ fH hd w m =>
      hObjRep_edgeDescent_eq V (WK V) (hWK V) ch chij e₀ fH hd w m
  · exact fun V v η hη a w => hObjRep_phi'_tmul WK hWK ch V v η hη a w

/-! ### `K`-rational structures exist — the `hWK` inhabitant  (G5, finding `V-S5G4-3`)

`RQ2-2.27`, `RQ2-2.28` and `RQ2-2.29` all take the family of `K`-rational structures `W_{i,K} ⊆ W_i`
as an **argument** `WK` together with its defining property `hWK` (`IsKRationalStructure`, the
`V-S5b-2` repair: without it `WK i := ⊥` refutes the rows).  That is faithful — the source's `H`
depends on the choice, which is the sense in which the census note says "up to natural
isomorphism" — but it leaves the whole family of rows conditional until something inhabits `hWK`.
Nothing did, which is one half of the G4 finding `V-S5G4-3`(c).

The inhabitant is ordinary linear algebra and needs no Galois input: `L_i` is a field, `W_i` is a
finite-dimensional `L_i`-vector space, and the `K`-span of an `L_i`-basis is a `K`-form.  The proof
is the two-line version of that sentence: an `L_i`-basis is `K`-linearly independent
(`LinearIndependent.restrict_scalars`, because `K → L_i` is injective), so it is a `K`-basis of its
own `K`-span (`Basis.span`); base-changing that `K`-basis gives an `L_i`-basis of
`L_i ⊗_K W_{i,K}` (`Basis.baseChange`) which the canonical map `a ⊗ w ↦ a · w` sends to the
original basis, so that map is a bijection.

@census none (G5 inhabitant for `IsKRationalStructure`; the `hWK` half of `V-S5G4-3`(c))
-/

/-- **G5**: every `W_i` carries a `K`-rational structure — `IsKRationalStructure` is inhabited at
every object and every vertex orbit, so the `hWK` hypothesis of `RQ2-2.27`/`RQ2-2.28`/`RQ2-2.29` is
satisfiable and those rows are not conditional on an empty class.

@census none (G5 inhabitant for `IsKRationalStructure`) -/
theorem exists_isKRationalStructure (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit) :
    ∃ WKi : Submodule K (V.W i), IsKRationalStructure V i WKi := by
  classical
  haveI : Module.Finite (Γ.toSpecies.L i) (V.W i) := finite_L_W V i
  let b := Module.Free.chooseBasis (Γ.toSpecies.L i) (V.W i)
  have hinj : Function.Injective fun c : K => c • (1 : Γ.toSpecies.L i) := by
    intro c c' h
    simp only [Algebra.smul_def, mul_one] at h
    exact (algebraMap K (Γ.toSpecies.L i)).injective h
  have hli : LinearIndependent K (b : _ → V.W i) :=
    b.linearIndependent.restrict_scalars hinj
  refine ⟨Submodule.span K (Set.range (b : _ → V.W i)), ?_⟩
  set Wk := Submodule.span K (Set.range (b : _ → V.W i)) with hWkdef
  let bK : Module.Basis _ K ↥Wk := Module.Basis.span hli
  let e : (Γ.toSpecies.L i) ⊗[K] ↥Wk ≃ₗ[Γ.toSpecies.L i] V.W i :=
    (bK.baseChange (Γ.toSpecies.L i)).equiv b (Equiv.refl _)
  have hmap : LinearMap.liftBaseChange (Γ.toSpecies.L i)
      ((Wk.subtype).restrictScalars K) = (e : _ →ₗ[Γ.toSpecies.L i] _) := by
    refine (bK.baseChange (Γ.toSpecies.L i)).ext fun k => ?_
    have h1 : LinearMap.liftBaseChange (Γ.toSpecies.L i) ((Wk.subtype).restrictScalars K)
        ((bK.baseChange (Γ.toSpecies.L i)) k) = b k := by
      rw [Module.Basis.baseChange_apply, LinearMap.liftBaseChange_tmul]
      show (1 : Γ.toSpecies.L i) • ((bK k : V.W i)) = _
      rw [one_smul, Module.Basis.coe_span_apply]
    have h2 : (e : _ →ₗ[Γ.toSpecies.L i] _) ((bK.baseChange (Γ.toSpecies.L i)) k) = b k :=
      Module.Basis.equiv_apply (bK.baseChange (Γ.toSpecies.L i)) k b (Equiv.refl _)
    rw [h1, h2]
  show Function.Bijective (LinearMap.liftBaseChange (Γ.toSpecies.L i)
    ((Wk.subtype).restrictScalars K))
  rw [hmap]
  exact e.bijective

end RationalQuiver

end RationalQuivers
