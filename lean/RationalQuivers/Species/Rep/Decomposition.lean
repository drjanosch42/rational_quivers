import RationalQuivers.Descent.Galois
import RationalQuivers.Species.OfQuiver
import RationalQuivers.Species.Rep.Twist
import RationalQuivers.Species.ToQuiver
import RationalQuivers.Species.Rep.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.DirectSum.Module
import Mathlib.FieldTheory.Galois.Profinite

/-!
# §2.6, the decomposition lemmas: the §2.6 preamble as data, and `eq:Leepsilondecomposition`

Formalizes the opening of §2.6 of `latex/rational_quivers.tex` (census `RQ2-2.19`).

## The §2.6 preamble is **data**, not a header binder

Clause `RQ2-2.19-Hs1` is the post-freeze standing-hypothesis clause (census r6, `AN-32`): §2.6 opens
by *choosing*, for each vertex orbit `i` a representative `v_i`, for each edge orbit `ε` a
representative `e_ε`, and then `σ_ε, τ_ε ∈ G` with `s(e_ε) = σ_ε v_i` and `t(e_ε) = τ_ε v_j`
(`eq:endsofedgetranslations`). `CONVENTIONS.md` §3 (the r6 delta) is explicit that such a standing
hypothesis must be carried as a **field of a bundle**, never as a `variable` binder Lean is free to
drop. `RationalQuiver.EdgeChoice` is that bundle: the representatives `v_i`, `e_ε` are stage S4's
`vertexRep` / `edgeRep`, and `σ_ε`, `τ_ε` are its two data fields together with the two equations
that pin them. `EdgeChoice.choose` is the G5 inhabitant — the choice exists, because the ends of a
representative edge lie in the corresponding vertex orbits.

`[IsGalois K L]` additionally appears as a binder, because `Γ.VertexOrbit` and `Γ.EdgeOrbit` are
`orbitRel.Quotient`s that need it to elaborate; the *standing hypothesis* of `RQ2-2.19-Hs1` is
nonetheless carried by the argument `Γ`, whose `galois` field cannot be dropped. This is stage S4's
practice in `Species/OfQuiver.lean` and is unchanged here.

## Factor order

Both sides of `eq:Leepsilondecomposition` are written with the **field on the left**, mathlib's
order for a base change (`TensorProduct.leftModule` puts the auxiliary module structure on the left
factor only, and the `L`-structure both sides carry is exactly that one). The source writes
`V ⊗ L`; the objects are the same, and no clause depends on the order. Same disclosure as
`Species/Rep/Tensor.lean`'s.

## The twist, and where it sits

`census/NOTATION.md` §2 distinguishes the two sides on which a twist can be named:

* `V ⊗_{L(e_ε), η τ_ε^{-1}} L` — twist named **after** the ring, so it is on the `L` side. That is
  `Twist (L(e_ε)) (η τ_ε⁻¹) ⊗[L(e_ε)] V`, using `Species/Rep/Twist.lean`.
* `V ⊗_{τ_ε, L(v_j)} L` — twist named **before** the ring, the *mirror* twist, so it is on `V`'s
  side: `V`'s `L(v_j)`-action is through `τ_ε`. `V` is an arbitrary right `L(e_ε)`-space
  (clause `RQ2-2.19-H1`), so this is carried as an explicit hypothesis `hV` rather than by a second
  wrapper — which also keeps the twist **visible in the elaborated signature**, the lesson of
  finding **S5-F4**.

## Main definitions / results
* `RationalQuivers.RationalQuiver.EdgeChoice` (+ `.choose`, `.CosetIndex`, `.rep`) — the §2.6
  preamble as data, and the index set `G_{v_j}/G_{τ_ε^{-1}e_ε}` of `eq:Leepsilondecomposition`.
* `RationalQuivers.RationalQuiver.leEpsilon_decomposition` — census `RQ2-2.19`.
-/

universe u

namespace RationalQuivers

open MulAction

open scoped TensorProduct DirectSum

namespace RationalQuiver

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  (Γ : RationalQuiver K L)

/-- **The §2.6 preamble's choice** `eq:endsofedgetranslations`: for the chosen representative
`e_ε` of an edge orbit `ε ⊆ E_{ij}`, elements `σ_ε, τ_ε ∈ G` with `s(e_ε) = σ_ε v_i` and
`t(e_ε) = τ_ε v_j`.

Carried as a bundle, per `CONVENTIONS.md` §3: a standing hypothesis that must survive into a
signature is a field, never a binder.

@census none (the standing hypothesis of clause `RQ2-2.19-Hs1`, as data)
@clauses   RQ2-2.19-Hs1, RQ2-2.19-H2
-/
structure EdgeChoice {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) : Type u where
  /-- `σ_ε`. -/
  σ : Gal(L/K)
  /-- `τ_ε`. -/
  τ : Gal(L/K)
  /-- `s(e_ε) = σ_ε v_i`. -/
  source_eq : σ • Γ.vertexRep i = Γ.toRQuiver.source (Γ.edgeRep ε)
  /-- `t(e_ε) = τ_ε v_j`. -/
  target_eq : τ • Γ.vertexRep j = Γ.toRQuiver.target (Γ.edgeRep ε)

/-- **G5 inhabitant** of `EdgeChoice`: the choice the source makes exists, because the ends of the
chosen representative edge lie in the corresponding vertex orbits (stage S4's
`source_edgeRep_mem_orbit` / `target_edgeRep_mem_orbit`).

@census none (G5 inhabitant of `EdgeChoice`)
-/
noncomputable def EdgeChoice.choose {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) :
    Γ.EdgeChoice ε where
  σ := (Γ.source_edgeRep_mem_orbit ε).choose
  τ := (Γ.target_edgeRep_mem_orbit ε).choose
  source_eq := (Γ.source_edgeRep_mem_orbit ε).choose_spec
  target_eq := (Γ.target_edgeRep_mem_orbit ε).choose_spec

/-- `σ_ε⁻¹ s(e_ε) = v_i`: the source equation of `eq:endsofedgetranslations`, read backwards.
This is the form §2.6 uses — `σ_ε` translates the *chosen* representative `v_i` to the source of
the chosen edge, so its inverse pulls the edge's source back to `v_i` — and it is the projection
that keeps `source_eq` live.

@census none (clause witness for `RQ2-2.19-H2`)
@clauses   RQ2-2.19-H2
-/
theorem EdgeChoice.inv_smul_source {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) :
    ch.σ⁻¹ • Γ.toRQuiver.source (Γ.edgeRep ε) = Γ.vertexRep i := by
  rw [← ch.source_eq, inv_smul_smul]

/-- `τ_ε⁻¹ t(e_ε) = v_j`, the target half.  It is also what makes `τ_ε⁻¹ e_ε` — the edge appearing
in the index set `G_{v_j}/G_{τ_ε^{-1}e_ε}` below — an edge *at* `v_j`.

@census none (clause witness for `RQ2-2.19-H2`)
@clauses   RQ2-2.19-H2
-/
theorem EdgeChoice.inv_smul_target {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) :
    ch.τ⁻¹ • Γ.toRQuiver.target (Γ.edgeRep ε) = Γ.vertexRep j := by
  rw [← ch.target_eq, inv_smul_smul]

/-- **Clause `RQ2-2.19-C2`**: the index set of `eq:Leepsilondecomposition` is the coset space
`G_{v_j} / G_{τ_ε^{-1} e_ε}`, the smaller stabilizer sitting inside the larger by
`Subgroup.subgroupOf`.

@census none (clause witness for `RQ2-2.19-C2`)
@clauses   RQ2-2.19-C2
-/
abbrev EdgeChoice.CosetIndex {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) : Type u :=
  (stabilizer Gal(L/K) (Γ.vertexRep j)) ⧸
    ((stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε)).subgroupOf
      (stabilizer Gal(L/K) (Γ.vertexRep j)))

/-- The "system of representatives for `G_{v_j}/G_{τ_ε^{-1}e_ε}`" the source chooses.

@census none (helper for `RQ2-2.19-C1`)
-/
noncomputable def EdgeChoice.rep {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch) : Gal(L/K) :=
  ((Quotient.out η : stabilizer Gal(L/K) (Γ.vertexRep j)) : Gal(L/K))

/-- The vertex `η τ_ε^{-1} σ_ε v_i` indexed by a coset `η`, the `(ε,η)`-summand's home in
`eq:WiiMjL`.  An `abbrev`, so that the displays of `RQ2-2.20`/`RQ2-2.22` and the formula of
`RQ2-2.23` elaborate to one and the same type.

@census none (helper)
-/
@[reducible] noncomputable def EdgeChoice.cosetVertex {i j : Γ.VertexOrbit}
    {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch) : Γ.V :=
  (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ) • Γ.vertexRep i

/-! ### `RQ2-2.21` — extension of scalars along a Galois twist

From here `Γ` is implicit: every declaration below takes a representation `M : Rep Γ`, which
determines it.
-/

variable {Γ}

/-- **`W_v := M(v)^{G_v}`**, the invariants of the continuous semi-linear `G_v`-action on `M(v)`,
as a vector space over the fixed field `L(v) = L^{G_v}` (the source's `eq:abusivedefinitionofLv`).

`stabField K L v` is stage S4's `L(v)`; the `L(v)`-structure is the restriction of `M(v)`'s
`L`-structure, and the fixed set is stable under it precisely because `L(v)` is the fixed field of
`G_v` and each `φ_{v,σ}` is `σ`-semi-linear.

@census none (helper: `W_i` of clauses `RQ2-2.20-H1`, `RQ2-2.21-C1`, `RQ2-2.26-H2`)
@clauses   RQ2-2.21-C1
-/
def Rep.vertexFixed (M : Rep Γ) (v : Γ.V) : Submodule ↥(stabField K L v) (M.M v) where
  carrier := {m | ∀ σ : stabilizer Gal(L/K) v, M.φ' (σ : Gal(L/K)) σ.2 m = m}
  add_mem' {a b} ha hb σ := by rw [map_add, ha σ, hb σ]
  zero_mem' σ := by rw [map_zero]
  smul_mem' c {m} hm σ := by
    have hc : ∀ x : M.M v, c • x = (c : L) • x := fun _ => rfl
    rw [hc, Rep.φ'_smul, hm σ, ← hc]
    congr 1
    exact (IntermediateField.mem_fixedField_iff _ _).mp c.2 _ σ.2

/-! ### Reading an `E`-module over the respelled base  (finding **S5-F5**)

`Twist E σ ⊗[TwistBase E σ] W` needs `W` to be a `TwistBase E σ`-module.  On the `W` side the
action is **untwisted** — it is `E`'s own action, read through the ring isomorphism
`TwistBase.toE` — and that is correct: the source twists only the `L` factor.

These instances are deliberately **not** stated generically for all `W` with `[Module ↥E W]`.  A
generic instance would fire for `W := Twist E σ` itself, which does carry an (untwisted)
`Module ↥E`, and would then compete with `Twist.algebraBase` — re-creating finding **S5-F5** one
level up.  Each instance below is keyed to a specific carrier that is *not* a `Twist`, so no
competition is possible; the guards in `Species/Rep/Twist.lean` keep that honest.

@census none (helpers, S5-F5 repair)
-/

/-- `W_v` over the respelled base, untwisted.  @census none (helper) -/
noncomputable instance Rep.moduleTwistBase_vertexFixed (M : Rep Γ) (v : Γ.V) (σ : Gal(L/K)) :
    Module (Twist.TwistBase (stabField K L v) σ) ↥(M.vertexFixed v) :=
  Module.compHom _ (Twist.TwistBase.toE)

/-- `W_i` over the respelled base at the species head — the `S5-F3` boundary again.
@census none (helper) -/
noncomputable instance Rep.moduleTwistBase_W (M : Rep Γ) (i : Γ.VertexOrbit) (σ : Gal(L/K)) :
    Module (Twist.TwistBase (Γ.vertexOrbitField i) σ) ↥(M.vertexFixed (Γ.vertexRep i)) :=
  M.moduleTwistBase_vertexFixed (Γ.vertexRep i) σ

/-! ### `RQ2-2.19`'s well-definedness identity  (G4)

`leEpsilon_decomposition`'s map sends `a ⊗ v` to the constant family `(ofL a ⊗ v)_η`.  For that to
be well defined over `L(v_j)` one needs, for `b ∈ L(v_j)`,

  `(η τ_ε⁻¹)( ι(b) ) = b`   where `ι = edgeComponentRight ε : L(v_j) → L(e_ε)`,

i.e. the twist `η τ_ε⁻¹` undoes the canonical embedding.  Both halves are in-tree facts:
`ι` is "apply any `σ` with `σ · v_j = t(e_ε)`", and `ch.τ` is such a `σ` (`ch.target_eq`); then
`η τ_ε⁻¹ τ_ε = η` fixes `L(v_j)` because `η ∈ G_{v_j}` and `L(v_j) = L^{G_{v_j}}`.

@census none (G4 engine for `RQ2-2.19`)
-/

/-- `edgeComponentRight` is "apply `τ_ε`".

S3 gives it as "apply the `choose`" (`edgeComponentRight_coe`); `stabField_apply_eq_of_smul_eq` is
exactly the statement that the choice does not matter, and `ch.target_eq` says `τ_ε` is a legitimate
alternative.  @census none (helper for `RQ2-2.19`) -/
theorem edgeComponentRight_coe_tau {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (b : ↥(Γ.vertexOrbitField j)) :
    ((Γ.edgeComponentRight ε b : ↥(Γ.edgeOrbitField ε)) : L) = ch.τ (b : L) := by
  rw [Γ.edgeComponentRight_coe ε b]
  exact stabField_apply_eq_of_smul_eq
    (((mem_orbit_iff.mp (Γ.target_edgeRep_mem_orbit ε)).choose_spec).trans ch.target_eq.symm) b

/-- **`RQ2-2.19`'s well-definedness identity**: the twist `η τ_ε⁻¹` undoes `edgeComponentRight`.

This is what makes `leEpsilon_decomposition`'s map — `a ⊗ v ↦ (ofL a ⊗ v)_η`, the *constant* family
— balanced over `L(v_j)`.  `τ_ε⁻¹` returns `ι(b)` to `b`, and `η ∈ G_{v_j}` then fixes it because
`L(v_j) = L^{G_{v_j}}`.

@census none (helper for `RQ2-2.19`) -/
theorem twist_edgeComponentRight {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch) (b : ↥(Γ.vertexOrbitField j)) :
    (EdgeChoice.rep Γ ch η * ch.τ⁻¹)
        ((Γ.edgeComponentRight ε b : ↥(Γ.edgeOrbitField ε)) : L) = (b : L) := by
  rw [edgeComponentRight_coe_tau ch b, AlgEquiv.mul_apply]
  show EdgeChoice.rep Γ ch η (ch.τ⁻¹ (ch.τ (b : L))) = (b : L)
  rw [show ch.τ⁻¹ (ch.τ (b : L)) = (b : L) from AlgEquiv.symm_apply_apply ch.τ (b : L)]
  exact (IntermediateField.mem_fixedField_iff _ _).mp b.2 _
    (Quotient.out η : stabilizer Gal(L/K) (Γ.vertexRep j)).2

/-! ### Finding **S5-F6** — `RQ2-2.19`'s `TwistBase` binder is unpinned  (G4, measured)

The `S5-F5` repair added the instance binder `[∀ τ, Module (TwistBase (L(e_ε)) τ) V]` to
`leEpsilon_decomposition` (`§24`'s delta row: *"new instance binder for `V`"*).  It added **no
hypothesis saying what that action is.**  `hV` relates the `L(v_j)`-action on `V` to the
`↥(L(e_ε))`-action; nothing relates either to the `TwistBase`-action, which is therefore a free
parameter of the statement — while the conclusion's tensor is balanced over exactly that action.

This is `S5-F5`'s own residue, and it is the shape `§26`/`§33` warn about from the other side: the
respelling introduced a new algebraic structure and pinned it on the `Twist` side (`smul_base_def`,
`#synth` guards) but left it unpinned on the `V` side, where it is a *hypothesis* rather than an
instance the module supplies.

**Two measurements, not an impression.**

1. `exact?` cannot prove `b • v = (b.val : ↥(L(e_ε))) • v` in `leEpsilon_decomposition`'s exact
   context — the action is not determined there.
2. `leEpsilon_decomposition_entails_untwisted_base` below **compiles**: the row's own conclusion
   *entails* the missing fact.  So the fact is not an artifact of one proof strategy; any proof of
   the row proves it, and a `V` violating it refutes the row.

**Consequence.** `RQ2-2.19` is not provable as frozen.  The minimal repair is one hypothesis —
"the respelled base acts on `V` through `TwistBase.toE`" — which is what `§`'s
`Rep.moduleTwistBase_vertexFixed` (`Module.compHom _ TwistBase.toE`) already satisfies by `rfl`, so
`RQ2-2.20`, the only consumer, pays nothing.  **Statements are frozen: this is reported to the
coordinator and booked in `§24`, not repaired here.**

A full refutation — a concrete `Γ` and a `V` whose `TwistBase`-action disagrees with its
`↥(L(e_ε))`-action on the image of `edgeComponentRight` — is *not* compiled below; it needs a
worked rational quiver with a non-trivial edge extension.  What is compiled is the entailment,
which is what makes the hypothesis necessary rather than convenient.

@census none (finding **S5-F6** artifact)
-/

omit [IsGalois K L] in
/-- Over a field, `w ↦ (1 : Twist E σ) ⊗ₜ w` is injective.

`Twist E σ` is a `TwistBase E σ`-vector space and `algebraMap` is injective, so it has a linear
retraction `g` with `g 1 = 1` (`LinearMap.exists_leftInverse_of_injective`); `rTensor g` followed
by `TensorProduct.lid` then sends `1 ⊗ₜ w` back to `w`.

@census none (finding **S5-F6** artifact) -/
theorem tmul_one_eq_zero (E : IntermediateField K L) (σ : Gal(L/K))
    (V : Type u) [AddCommGroup V] [Module (Twist.TwistBase E σ) V] {w : V}
    (h : (1 : Twist E σ) ⊗ₜ[Twist.TwistBase E σ] w = 0) : w = 0 := by
  obtain ⟨g, hg⟩ :=
    (Algebra.linearMap (Twist.TwistBase E σ) (Twist E σ)).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (algebraMap (Twist.TwistBase E σ) (Twist E σ)).injective)
  have h1 : g 1 = 1 := by
    have := congrArg (fun f => f (1 : Twist.TwistBase E σ)) hg
    simpa only [show (Twist.ofL 1 : Twist E σ) = 1 from rfl, map_one, LinearMap.coe_comp,
      Function.comp_apply, Algebra.linearMap_apply, LinearMap.id_coe, id_eq] using this
  have := congrArg (fun z => TensorProduct.lid (Twist.TwistBase E σ) V (LinearMap.rTensor V g z)) h
  simpa [h1] using this

/-- **Finding `S5-F6`, compiled.**  `leEpsilon_decomposition`'s conclusion *entails* that the
respelled base acts on `V` through `edgeComponentRight` — a fact the row's hypotheses do not
supply.

The derivation is the row's own balance condition read backwards.  In the source
`L ⊗_{L(v_j)} V` one has `(b • 1) ⊗ v = 1 ⊗ (b • v)`; pushing both sides through `e` and its
pinning clause `C3` turns this into
`ofL (b·1) ⊗ v = ofL 1 ⊗ (b • v)` in the `η`-summand, and `twist_edgeComponentRight` identifies
`ofL (b·1)` with `β • ofL 1` for `β := ofE (edgeComponentRight b)`.  Moving `β` across the tensor
and cancelling `1 ⊗ ·` (`tmul_one_eq_zero`) leaves `β • v = b • v`.

Nothing in `leEpsilon_decomposition`'s context proves that (`exact?` fails on it), so the row needs
it as a hypothesis.  Note `hV` is **not** used: the entailment is against the `L(v_j)`-action
directly, and `hV` only re-reads the right-hand side as the `↥(L(e_ε))`-action.

@census none (finding **S5-F6** artifact) -/
theorem leEpsilon_decomposition_entails_untwisted_base {i j : Γ.VertexOrbit}
    {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε)
    (V : Type u) [AddCommGroup V] [Module ↥(Γ.edgeOrbitField ε) V]
    [Module ↥(Γ.vertexOrbitField j) V]
    [∀ τ : Gal(L/K), Module (Twist.TwistBase (Γ.edgeOrbitField ε) τ) V]
    (hconc : ∃ e : (L ⊗[↥(Γ.vertexOrbitField j)] V) ≃ₗ[L]
        (∀ η : EdgeChoice.CosetIndex Γ ch,
          Twist (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)
            ⊗[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)] V),
      ∀ (a : L) (v : V) (η : EdgeChoice.CosetIndex Γ ch),
        e (a ⊗ₜ[↥(Γ.vertexOrbitField j)] v) η
          = Twist.ofL a
              ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)] v)
    (η : EdgeChoice.CosetIndex Γ ch) (b : ↥(Γ.vertexOrbitField j)) (v : V) :
    (Twist.TwistBase.ofE (Γ.edgeComponentRight ε b) :
        Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)) • v = b • v := by
  obtain ⟨e, he⟩ := hconc
  set ρ := EdgeChoice.rep Γ ch η * ch.τ⁻¹ with hρ
  set β : Twist.TwistBase (Γ.edgeOrbitField ε) ρ :=
    Twist.TwistBase.ofE (Γ.edgeComponentRight ε b) with hβ
  have hsrc : (b • (1 : L)) ⊗ₜ[↥(Γ.vertexOrbitField j)] v
      = (1 : L) ⊗ₜ[↥(Γ.vertexOrbitField j)] (b • v) := TensorProduct.smul_tmul _ _ _
  have hpush := congrArg (fun z => e z η) hsrc
  simp only [he] at hpush
  have hscal : (Twist.ofL (b • (1 : L)) : Twist (Γ.edgeOrbitField ε) ρ)
      = β • (Twist.ofL (1 : L)) := by
    rw [Twist.smul_base_def]
    congr 1
    rw [hβ]
    show ((b : L) * 1) = ρ ((Γ.edgeComponentRight ε b : ↥(Γ.edgeOrbitField ε)) : L) * 1
    rw [twist_edgeComponentRight ch η b]
  rw [hscal, TensorProduct.smul_tmul] at hpush
  have hz : (1 : Twist (Γ.edgeOrbitField ε) ρ)
      ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] (β • v - b • v) = 0 := by
    rw [TensorProduct.tmul_sub, sub_eq_zero]
    exact hpush
  exact sub_eq_zero.mp (tmul_one_eq_zero (Γ.edgeOrbitField ε) ρ V hz)

/-! ### `RQ2-2.19` sub-obligation (1): cosets give embeddings

Each coset `η ∈ G_{v_j}/(G_{τ_ε⁻¹ e_ε} ∩ G_{v_j})` gives an `L(v_j)`-algebra embedding
`L(e_ε) → L`, namely `x ↦ (η τ_ε⁻¹)(x)`.

* It is `L(v_j)`-linear by `twist_edgeComponentRight` — the identity proved above.
* It is **independent of the coset representative**: changing `η` by `h ∈ G_{τ_ε⁻¹ e_ε}` changes the
  map by `h` acting on `τ_ε⁻¹ L(e_ε) = L(τ_ε⁻¹ e_ε)` (`stabField_map_smul`), which `h` fixes.
* It is **injective**: if two cosets give the same embedding then their ratio fixes
  `L(τ_ε⁻¹ e_ε)` pointwise, hence lies in `G_{τ_ε⁻¹ e_ε}` by the Galois correspondence
  (`fixingSubgroup_stabField_E`, using `RQ2-1.02-C3`), hence the cosets are equal.

@census none (G4 engine for `RQ2-2.19`)
-/

/-- `τ_ε⁻¹` carries `L(e_ε)` onto `L(τ_ε⁻¹ e_ε)`.  @census none (helper) -/
theorem map_tau_inv_edgeOrbitField {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) :
    IntermediateField.map ((ch.τ⁻¹ : Gal(L/K)) : L →ₐ[K] L) (stabField K L (Γ.edgeRep ε))
      = stabField K L (ch.τ⁻¹ • Γ.edgeRep ε) :=
  stabField_map_smul _ _

/-- An element of `G_{τ_ε⁻¹ e_ε}` fixes `τ_ε⁻¹(L(e_ε))` pointwise.  @census none (helper) -/
theorem fix_of_mem_stabilizer_tau {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) {h : Gal(L/K)}
    (hh : h ∈ stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε))
    (x : ↥(Γ.edgeOrbitField ε)) : h (ch.τ⁻¹ (x : L)) = ch.τ⁻¹ (x : L) := by
  have hmem : ch.τ⁻¹ (x : L) ∈ stabField K L (ch.τ⁻¹ • Γ.edgeRep ε) := by
    rw [← map_tau_inv_edgeOrbitField ch, IntermediateField.mem_map]
    exact ⟨(x : L), x.2, rfl⟩
  exact (IntermediateField.mem_fixedField_iff _ _).mp hmem _ hh

/-! ### `RQ2-2.19` sub-obligation (2): the count

`τ_ε⁻¹ e_ε` is the edge translated so that its **target is `v_j`** (`ch.target_eq` gives
`τ_ε · v_j = t(e_ε)`, so `t(τ_ε⁻¹ e_ε) = v_j`).  That makes `L(v_j) ⊆ L(τ_ε⁻¹ e_ε)` a genuine
intermediate-field inclusion — which `L(v_j) ⊆ L(e_ε)` is **not**: the map there is
`edgeComponentRight`, i.e. "apply `τ_ε`", not an inclusion.  Working with `τ_ε⁻¹ e_ε` is what turns
the count into mathlib's `IntermediateField.finrank_eq_fixingSubgroup_index`.

@census none (G4 engine for `RQ2-2.19`)
-/

/-- `t(τ_ε⁻¹ e_ε) = v_j`.  @census none (helper) -/
theorem target_tau_inv_edgeRep {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) :
    Γ.toRQuiver.target (ch.τ⁻¹ • Γ.edgeRep ε) = Γ.vertexRep j := by
  rw [Γ.target_smul, ← ch.target_eq, inv_smul_smul]

/-- **`L(v_j) ⊆ L(τ_ε⁻¹ e_ε)`** — a genuine inclusion, unlike `L(v_j) → L(e_ε)`.

The stabiliser of an edge is contained in that of its target (`stabilizer_le_target`), and
`t(τ_ε⁻¹ e_ε) = v_j`; `stabField_le_of_stabilizer_le` then reverses the inclusion on fixed fields.

@census none (helper for `RQ2-2.19-C2`) -/
theorem vertexOrbitField_le_tau_inv {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) :
    stabField K L (Γ.vertexRep j) ≤ stabField K L (ch.τ⁻¹ • Γ.edgeRep ε) := by
  have h0 := Γ.stabilizer_le_target (ch.τ⁻¹ • Γ.edgeRep ε)
  rw [target_tau_inv_edgeRep ch] at h0
  -- `stabField_le_of_stabilizer_le` types both points in ONE `MulAction`; here they are a
  -- vertex and an edge, so we go to the mathlib lemma it is built from.
  exact IntermediateField.fixedField_le h0

/-! ### The semi-linear `G_v`-action on `M(v)`  (G4 engine for `RQ2-2.21`)

`RQ2-2.21` is Galois descent for the extension `L / L(v)`, so the first thing needed is the object
it descends: `M(v)` carrying the action of `G_v = stabilizer Gal(L/K) v` by the transported
structure maps `φ'_{v,σ}`, which land back in `M(v)` exactly because `σ` fixes `v`.

Its `MulAction` laws are `φ'_one` and `φ'_comp`; semi-linearity over `L` is `φ'_smul`; and the
open-stabilizer continuity comes from `Rep.smooth` (clause `RQ2-1.08-C6`), which is stated jointly
on the vertex and the fibre and so already contains the fibrewise statement.

@census none (helpers for `RQ2-2.21`)
-/

/-- The `G_v`-action on `M(v)`: `σ • m := φ'_{v,σ}(m)`, well defined because `σ • v = v`.
@census none (helper) -/
instance Rep.vertexMulAction (M : Rep Γ) (v : Γ.V) :
    MulAction (stabilizer Gal(L/K) v) (M.M v) where
  smul σ m := M.φ' (σ : Gal(L/K)) σ.2 m
  one_smul m := by
    show M.φ' (1 : Gal(L/K)) _ m = m
    rw [M.φ'_one]
    rfl
  mul_smul σ τ m := by
    show M.φ' ((σ * τ : stabilizer Gal(L/K) v) : Gal(L/K)) _ m
        = M.φ' (σ : Gal(L/K)) _ (M.φ' (τ : Gal(L/K)) _ m)
    exact (M.φ'_comp (σ : Gal(L/K)) (τ : Gal(L/K)) τ.2 σ.2 _ m).symm

/-- The action of `RQ2-2.21`'s engine, unfolded.  @census none (helper) -/
theorem Rep.vertexMulAction_smul (M : Rep Γ) (v : Γ.V) (σ : stabilizer Gal(L/K) v)
    (m : M.M v) : σ • m = M.φ' (σ : Gal(L/K)) σ.2 m := rfl

/-- `G_v` acts by additive maps.  @census none (helper) -/
instance Rep.vertexDistribMulAction (M : Rep Γ) (v : Γ.V) :
    DistribMulAction (stabilizer Gal(L/K) v) (M.M v) where
  smul_zero σ := map_zero (M.φ' (σ : Gal(L/K)) σ.2)
  smul_add σ a b := map_add (M.φ' (σ : Gal(L/K)) σ.2) a b

/-- Semi-linearity of the `G_v`-action (clause `RQ2-1.08-C4`, restricted).  @census none (helper) -/
theorem Rep.vertexMulAction_smul_smul (M : Rep Γ) (v : Γ.V) (σ : stabilizer Gal(L/K) v)
    (a : L) (m : M.M v) : σ • (a • m) = (σ : Gal(L/K)) a • (σ • m) :=
  M.φ'_smul (σ : Gal(L/K)) σ.2 a m

/-- `RQ2-2.21-C1` in fixed-point form: `W_v` is exactly the `G_v`-invariants of `M(v)`.

This is the identification that lets `Descent/Galois.lean`'s `fixedPoints` be used for
`Rep.vertexFixed`; it is definitional, and is stated so that the descent step can rewrite along it.

@census none (helper)
@clauses   RQ2-2.21-C1
-/
theorem Rep.mem_vertexFixed_iff (M : Rep Γ) (v : Γ.V) (m : M.M v) :
    m ∈ M.vertexFixed v ↔ ∀ σ : stabilizer Gal(L/K) v, σ • m = m := Iff.rfl

/-- The fibrewise open-stabilizer condition, extracted from the joint one (`RQ2-1.08-C6`).

`Rep.smooth` says the set of `σ` fixing the pair `⟨v, m⟩` is open; that set is precisely the set of
`σ` with `σ • v = v` *and* `φ'_{v,σ}(m) = m`, i.e. the stabilizer of `m` inside `G_v` seen in
`Gal(L/K)`.  This is the form the descent step consumes, and it is why `RQ2-2.21` needs no
continuity hypothesis of its own.

@census none (helper for `RQ2-2.21`)
-/
theorem Rep.isOpen_fibre_stabilizer (M : Rep Γ) (v : Γ.V) (m : M.M v) :
    IsOpen {σ : Gal(L/K) | ∃ h : σ • v = v, M.φ' σ h m = m} := by
  have hset : {σ : Gal(L/K) | ∃ h : σ • v = v, M.φ' σ h m = m}
      = {σ : Gal(L/K) | (⟨σ • v, M.φ σ v m⟩ : (w : Γ.V) × M.M w) = ⟨v, m⟩} := by
    ext σ
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hv, hm⟩
      exact (M.sigma_mk_eq_iff hv _ _).mpr hm
    · intro hσ
      have hv : σ • v = v := congrArg Sigma.fst hσ
      exact ⟨hv, (M.sigma_mk_eq_iff hv _ _).mp hσ⟩
  rw [hset]
  exact M.smooth ⟨v, m⟩

/-! ### `G_v = Gal(L/L(v))`  — the Galois correspondence at a vertex

The descent in `RQ2-2.21` is over `L / L(v)`, so its group is `Gal(L/L(v))`; the action built above
is by `G_v = stabilizer Gal(L/K) v`.  These are the same group, and this is exactly the point at
which the *continuity* hypothesis earns its keep: the identification is the Galois correspondence
`(L^H)^{fix} = H`, which holds for a **closed** subgroup, and `G_v` is closed because
`RQ2-1.02-C2` makes it open (`Γ.isOpen_stabilizer_V`).

For finite `L/K` this is `IsGalois.fixingSubgroup_fixedField` and the topology is invisible.  For
infinite `L/K` it is `InfiniteGalois.fixingSubgroup_fixedField` and the smoothness clause is
load-bearing — without it `L(v)` would still be defined but would not recover `G_v`, and the
descent would be false.  This is the mathematical content of `census/NOTATION.md` §12.

@census none (helpers for `RQ2-2.21`)
-/

/-- The Galois correspondence at **any** point with an open stabiliser: `L(x)` fixes exactly `G_x`.

Generalises `fixingSubgroup_stabField` off the vertex set, so that the edge case (`RQ2-1.02-C3`)
reuses it rather than repeating the argument.  @census none (helper) -/
theorem fixingSubgroup_stabField_of_isOpen {X : Type u} [MulAction Gal(L/K) X] (x : X)
    (hx : IsOpen ((stabilizer Gal(L/K) x : Subgroup Gal(L/K)) : Set Gal(L/K))) :
    (stabField K L x).fixingSubgroup = stabilizer Gal(L/K) x :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨_, Subgroup.isClosed_of_isOpen _ hx⟩

/-- The edge case of the correspondence — `RQ2-1.02-C3` in place of `C2`.  @census none (helper) -/
theorem fixingSubgroup_stabField_E (e : Γ.E) :
    (stabField K L e).fixingSubgroup = stabilizer Gal(L/K) e :=
  fixingSubgroup_stabField_of_isOpen e (Γ.isOpen_stabilizer_E e)

/-- `G_v` is a closed subgroup of `Gal(L/K)`: it is open by `RQ2-1.02-C2`.  @census none (helper) -/
theorem isClosed_stabilizer_V (v : Γ.V) :
    IsClosed ((stabilizer Gal(L/K) v : Subgroup Gal(L/K)) : Set Gal(L/K)) :=
  Subgroup.isClosed_of_isOpen _ (Γ.isOpen_stabilizer_V v)

/-- **The Galois correspondence at a vertex**: `L(v)` fixes exactly `G_v`.

`L(v) = L^{G_v}` by definition, and `(L^{G_v})^{fix} = G_v` because `G_v` is closed.  This is the
step that makes `RQ2-2.21` true for infinite `L/K`.

@census none (helper for `RQ2-2.21`)
-/
theorem fixingSubgroup_stabField (v : Γ.V) :
    (stabField K L v).fixingSubgroup = stabilizer Gal(L/K) v :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨stabilizer Gal(L/K) v, Γ.isClosed_stabilizer_V v⟩

/-- An `L(v)`-automorphism of `L`, read in `Gal(L/K)`, fixes `v`.  @census none (helper) -/
theorem restrictScalars_mem_stabilizer (v : Γ.V) (σ : Gal(L/↥(stabField K L v))) :
    σ.restrictScalars K ∈ stabilizer Gal(L/K) v := by
  rw [← Γ.fixingSubgroup_stabField v]
  exact ((IntermediateField.fixingSubgroupEquiv (stabField K L v)).symm σ).2

/-- `Gal(L/L(v)) ≃* G_v`, the correspondence in the form `RQ2-2.21`'s descent consumes.

@census none (helper for `RQ2-2.21`)
-/
noncomputable def galStabFieldEquiv (v : Γ.V) :
    Gal(L/↥(stabField K L v)) ≃* stabilizer Gal(L/K) v :=
  (IntermediateField.fixingSubgroupEquiv (stabField K L v)).symm.trans
    (MulEquiv.subgroupCongr (Γ.fixingSubgroup_stabField v))

@[simp]
theorem galStabFieldEquiv_coe (v : Γ.V) (σ : Gal(L/↥(stabField K L v))) :
    ((Γ.galStabFieldEquiv v σ : stabilizer Gal(L/K) v) : Gal(L/K)) = σ.restrictScalars K := rfl

/-! ### `RQ2-2.19` sub-obligation (2): the count, concluded

`L(v_j) ⊆ L(τ_ε⁻¹ e_ε)` (`vertexOrbitField_le_tau_inv`) read as an intermediate field of
`L / L(v_j)` is `tauEdgeField`; mathlib's `IntermediateField.finrank_eq_fixingSubgroup_index` then
computes `[L(τ_ε⁻¹ e_ε) : L(v_j)]` as the index of a fixing subgroup inside `Gal(L/L(v_j))`, and
the Galois correspondence at an **edge** identifies that fixing subgroup with the coset index set
of clause `RQ2-2.19-C2`.

Stated in **membership** form: the subgroup-equality form has to be pushed through
`(galStabFieldEquiv _).toMonoidHom`, where `Subgroup.mem_comap` does not fire.

@census none (G4 engine for `RQ2-2.19`)
-/

/-- `L(τ_ε⁻¹ e_ε)`, read as an intermediate field of `L / L(v_j)`.

This is the object the count is about: `L(v_j) ⊆ L(τ_ε⁻¹ e_ε)` is a genuine inclusion of
intermediate fields (`vertexOrbitField_le_tau_inv`), so `extendScalars` re-bases it.

@census none (helper for `RQ2-2.19-C2`) -/
noncomputable def tauEdgeField {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) : IntermediateField ↥(Γ.vertexOrbitField j) L :=
  IntermediateField.extendScalars (Γ.vertexOrbitField_le_tau_inv ch)

/-- **The Galois correspondence at `τ_ε⁻¹ e_ε`, in membership form.**  An `L(v_j)`-automorphism of
`L` fixes `L(τ_ε⁻¹ e_ε)` pointwise **iff** its image in `Gal(L/K)` stabilises the edge
`τ_ε⁻¹ e_ε`.

Four in-tree ingredients, no new mathematics: `IntermediateField.mem_fixingSubgroup_iff` unfolds
both fixing-subgroup memberships to "fixes every element"; `galStabFieldEquiv_coe` says the image
of `σ` in `Gal(L/K)` is `σ.restrictScalars K`, so the two "fixes every element" statements are
about the same function; `fixingSubgroup_stabField_E` (clause `RQ2-1.02-C3`, via
`fixingSubgroup_stabField_of_isOpen`) turns membership in the edge stabiliser into membership in
`(L(τ_ε⁻¹ e_ε)).fixingSubgroup`; and `IntermediateField.mem_extendScalars` is `Iff.rfl`, so
membership in `tauEdgeField ch` and in `L(τ_ε⁻¹ e_ε)` need no transport.

Stated as an `↔` rather than as a subgroup equality over `Gal(L/K)`: the equality form has to be
read through `(galStabFieldEquiv _).toMonoidHom`, and `Subgroup.mem_comap` will not fire through
it.  The comap form that the index computation actually needs is `fixingSubgroup_tauEdgeField`
below, which is this lemma plus `ext`.

@census none (helper for `RQ2-2.19-C2`) -/
theorem mem_fixingSubgroup_tauEdgeField {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (σ : Gal(L/↥(Γ.vertexOrbitField j))) :
    σ ∈ (tauEdgeField ch).fixingSubgroup
      ↔ ((Γ.galStabFieldEquiv (Γ.vertexRep j) σ :
            stabilizer Gal(L/K) (Γ.vertexRep j)) : Gal(L/K))
          ∈ stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε) := by
  rw [IntermediateField.mem_fixingSubgroup_iff, Γ.galStabFieldEquiv_coe,
    ← fixingSubgroup_stabField_E (Γ := Γ) (ch.τ⁻¹ • Γ.edgeRep ε),
    IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h x hx => h x hx, fun h x hx => h x hx⟩

/-- `Gal(L/L(τ_ε⁻¹ e_ε)) = (G_{τ_ε⁻¹ e_ε} ∩ G_{v_j})` pulled back along `Gal(L/L(v_j)) ≃ G_{v_j}`.

`mem_fixingSubgroup_tauEdgeField` with `ext`; `Subgroup.mem_comap` and `Subgroup.mem_subgroupOf`
are both `Iff.rfl`, so nothing is done here beyond packaging.

@census none (helper for `RQ2-2.19-C2`) -/
theorem fixingSubgroup_tauEdgeField {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) :
    (tauEdgeField ch).fixingSubgroup
      = ((stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε)).subgroupOf
          (stabilizer Gal(L/K) (Γ.vertexRep j))).comap
        (Γ.galStabFieldEquiv (Γ.vertexRep j)).toMonoidHom := by
  ext σ
  exact mem_fixingSubgroup_tauEdgeField ch σ

/-- **`RQ2-2.19` sub-obligation (2), the count.**  The coset space of clause `RQ2-2.19-C2` has
exactly `[L(τ_ε⁻¹ e_ε) : L(v_j)]` elements.

**This identification is not definitional, and supplying it *is* the counting argument**
(attributed to clause `RQ2-2.19-C2`, where a reader meets the index set).  `EdgeChoice.CosetIndex`
is `G_{v_j}/(G_{τ_ε⁻¹e_ε} ∩ G_{v_j})`, a quotient formed **inside `G_{v_j}`**; the finrank on the
right is, by `IntermediateField.finrank_eq_fixingSubgroup_index`, the index of a `fixingSubgroup`
inside `Gal(L/L(v_j))`.  The two agree only because `galStabFieldEquiv` — the Galois
correspondence at the **vertex** `v_j`, hence clause `RQ2-1.02-C2` and the smoothness hypothesis —
is an isomorphism `Gal(L/L(v_j)) ≃ G_{v_j}` carrying `(L(τ_ε⁻¹ e_ε)).fixingSubgroup` to
`G_{τ_ε⁻¹e_ε} ∩ G_{v_j}`, which is `fixingSubgroup_tauEdgeField` — the Galois correspondence at
the **edge**, hence clause `RQ2-1.02-C3`.  Both correspondences are used, at different points.
`Subgroup.index_comap_of_surjective` then transports the index across, and the residual step
`Nat.card (G_{v_j}/H) = H.index` is `rfl` (`Subgroup.index` is defined as that cardinal).

This is the hypothesis `hcard` of S3's `tensorPi_bijective`, which is what consumes it.

@census none (helper for `RQ2-2.19-C2`) -/
theorem card_cosetIndex_eq_finrank {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) :
    Nat.card (EdgeChoice.CosetIndex Γ ch)
      = Module.finrank ↥(Γ.vertexOrbitField j) ↥(tauEdgeField ch) :=
  ((congrArg Subgroup.index (fixingSubgroup_tauEdgeField ch)).trans
      (Subgroup.index_comap_of_surjective _
        (Γ.galStabFieldEquiv (Γ.vertexRep j)).surjective)).symm.trans
    (IntermediateField.finrank_eq_fixingSubgroup_index (tauEdgeField ch)).symm
/-! ### `RQ2-2.19` sub-obligation (3): the étale splitting, instantiated

This is `eq:Leepsilondecompositionpre` — the source's own intermediate step, the `V = L(e_ε)` case
from which the general `V` follows by tensoring over `L(e_ε)`.

The engine is S3's `EtaleSpecies.tensorPi_bijective` (`Species/ToQuiver.lean`), which needs three
things and no more: a **finite** index set, an **injective** family of `L(v_j)`-algebra embeddings,
and the **count** `Nat.card P = finrank`.  The count is `card_cosetIndex_eq_finrank` above; the
other two are here.

Everything is stated at `L(τ_ε⁻¹ e_ε)` (`tauEdgeField`) rather than at `L(e_ε)`, for the reason
§ gives: `L(v_j) ⊆ L(τ_ε⁻¹ e_ε)` is a genuine inclusion and `L(v_j) → L(e_ε)` is not.  The
embeddings are correspondingly `y ↦ η(y)` rather than `x ↦ (ητ_ε⁻¹)(x)`; the two families agree
under `τ_ε⁻¹ : L(e_ε) ≅ L(τ_ε⁻¹ e_ε)`, and the general-`V` assembly is where that identification
is paid.

@census none (G4 engine for `RQ2-2.19-C1`)
-/

/-- **Clause `RQ2-2.19-C1`'s embeddings.**  The coset `η` gives the `L(v_j)`-algebra embedding
`L(τ_ε⁻¹ e_ε) → L`, `y ↦ η(y)`.

`L(v_j)`-linearity is the only content and it is immediate here: `η ∈ G_{v_j}` and
`L(v_j) = L^{G_{v_j}}`, so `η` fixes the base pointwise.  (Written at `L(e_ε)` instead, the same
map reads `x ↦ (ητ_ε⁻¹)(x)` and linearity is `twist_edgeComponentRight` — the same fact, paid at
a different point.)

@census none (helper for `RQ2-2.19-C1`) -/
noncomputable def cosetEmb {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch) :
    ↥(tauEdgeField ch) →ₐ[↥(Γ.vertexOrbitField j)] L where
  toFun y := EdgeChoice.rep Γ ch η (y : L)
  map_one' := by simp
  map_mul' x y := by simp
  map_zero' := by simp
  map_add' x y := by simp
  commutes' b := by
    show EdgeChoice.rep Γ ch η ((b : L)) = (b : L)
    exact (IntermediateField.mem_fixedField_iff _ _).mp b.2 _
      (Quotient.out η : stabilizer Gal(L/K) (Γ.vertexRep j)).2

/-- **Distinct cosets give distinct embeddings** — the injectivity hypothesis of
`tensorPi_bijective`.

This is the Galois correspondence at the edge a second time (§'s third row).  If `η₁` and `η₂`
restrict to the same map on `L(τ_ε⁻¹ e_ε)` then `η₁⁻¹η₂` fixes it pointwise, so it lies in
`(L(τ_ε⁻¹ e_ε)).fixingSubgroup = G_{τ_ε⁻¹ e_ε}` (`fixingSubgroup_stabField_E`, clause
`RQ2-1.02-C3`); both representatives lie in `G_{v_j}`, so the ratio lies in the intersection, which
is exactly the subgroup the coset space is taken by.

@census none (helper for `RQ2-2.19-C1`) -/
theorem cosetEmb_injective {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) : Function.Injective (cosetEmb ch) := by
  intro η₁ η₂ h
  have hpt : ∀ y : ↥(tauEdgeField ch),
      EdgeChoice.rep Γ ch η₁ (y : L) = EdgeChoice.rep Γ ch η₂ (y : L) :=
    fun y => DFunLike.congr_fun h y
  have hmem : ((EdgeChoice.rep Γ ch η₁)⁻¹ * EdgeChoice.rep Γ ch η₂)
      ∈ stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε) := by
    rw [← fixingSubgroup_stabField_E (Γ := Γ) (ch.τ⁻¹ • Γ.edgeRep ε),
      IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    show (EdgeChoice.rep Γ ch η₁)⁻¹ (EdgeChoice.rep Γ ch η₂ y) = y
    rw [← hpt ⟨y, hy⟩]
    exact AlgEquiv.symm_apply_apply _ _
  rw [← Quotient.out_eq η₁, ← Quotient.out_eq η₂]
  exact Quotient.sound (QuotientGroup.leftRel_apply.mpr hmem)

/-- `L(τ_ε⁻¹ e_ε)` is finite over `L(v_j)` — the `Module.Finite` hypothesis of
`tensorPi_bijective`.

`L(τ_ε⁻¹ e_ε)` is finite over `K` because the edge stabiliser is open (`RQ2-2.09-C11`), and
`K ⊆ L(v_j) ⊆ L(τ_ε⁻¹ e_ε)` is a tower.  @census none (helper for `RQ2-2.19-C1`) -/
instance finite_tauEdgeField {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) :
    Module.Finite ↥(Γ.vertexOrbitField j) ↥(tauEdgeField ch) := by
  haveI : FiniteDimensional K ↥(tauEdgeField ch) :=
    finiteDimensional_stabField (K := K) (L := L) (ch.τ⁻¹ • Γ.edgeRep ε)
      (Γ.isOpen_stabilizer_E _)
  exact Module.Finite.of_restrictScalars_finite K _ _

/-- **`RQ2-2.19` sub-obligation (3), `eq:Leepsilondecompositionpre`.**  The canonical map
`L ⊗_{L(v_j)} L(τ_ε⁻¹ e_ε) → ∏_{η} L` is bijective.

S3's `tensorPi_bijective` verbatim, at `F := L(v_j)`, `A := L(τ_ε⁻¹ e_ε)`, `B := L`,
`P := EdgeChoice.CosetIndex`, `g := cosetEmb ch`.  Nothing is proved here that is not proved
above: the three hypotheses are `finite_tauEdgeField`, `cosetEmb_injective` and
`card_cosetIndex_eq_finrank`.  This is `CONVENTIONS.md` §6 rung 1 — the splitting engine already
exists and is used with its own spelling and generality.

`Finite (EdgeChoice.CosetIndex Γ ch)` is taken as an instance binder rather than resolved here:
the file's `finite_cosetIndex` (`RQ2-2.23-C6`'s first half) proves it, but sits later in the file,
and new material is placed by dependency.  Callers discharge it with that lemma.

@census none (helper for `RQ2-2.19-C1`) -/
theorem tensorPi_cosetEmb_bijective {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) [Finite (EdgeChoice.CosetIndex Γ ch)] :
    Function.Bijective (EtaleSpecies.tensorPi (cosetEmb ch)) :=
  EtaleSpecies.tensorPi_bijective (cosetEmb_injective ch) (card_cosetIndex_eq_finrank ch)

/-- `eq:Leepsilondecompositionpre` as an equivalence: `L ⊗_{L(v_j)} L(τ_ε⁻¹ e_ε) ≅ ∏_η L`, an
isomorphism of `L`-algebras.

@census none (helper for `RQ2-2.19-C1`) -/
noncomputable def leEpsilonPreEquiv {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) [Finite (EdgeChoice.CosetIndex Γ ch)] :
    (L ⊗[↥(Γ.vertexOrbitField j)] ↥(tauEdgeField ch)) ≃ₐ[L]
      (EdgeChoice.CosetIndex Γ ch → L) :=
  AlgEquiv.ofBijective _ (tensorPi_cosetEmb_bijective ch)

/-- `leEpsilonPreEquiv` on pure tensors: `a ⊗ y ↦ (a · η(y))_η`.  The pinning that the general-`V`
assembly propagates into clause `RQ2-2.19-C3`.  @census none (helper for `RQ2-2.19-C3`) -/
@[simp] theorem leEpsilonPreEquiv_tmul {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) [Finite (EdgeChoice.CosetIndex Γ ch)]
    (a : L) (y : ↥(tauEdgeField ch)) (η : EdgeChoice.CosetIndex Γ ch) :
    leEpsilonPreEquiv ch (a ⊗ₜ[↥(Γ.vertexOrbitField j)] y) η
      = a * EdgeChoice.rep Γ ch η (y : L) :=
  EtaleSpecies.tensorEval_tmul _ _ _

/-! ### `RQ2-2.19` sub-obligation (3′): the splitting, transported to `L(e_ε)`

Sub-obligation (3) is stated at `L(τ_ε⁻¹ e_ε)`, where `L(v_j)` sits by a genuine inclusion.  The
row is about `L(e_ε)`, over which `V` is a module.  `τ_ε⁻¹ : L(e_ε) ≅ L(τ_ε⁻¹ e_ε)` is the
identification, and **it is paid here, on the field** — the small object — rather than later on
`V`.  That is the whole reason for doing it at this point: transporting `V`'s module structure
instead would put a non-canonical `L(τ_ε⁻¹ e_ε)`-action on an arbitrary vector space and carry it
through every remaining step.

`L(v_j)`'s action on `L(e_ε)` is `edgeComponentRight`, which is **not** an `Algebra` instance in the
tree and deliberately is not made one: the mirror `edgeComponentLeft` would give a second
`Algebra ↥(Γ.vertexOrbitField ?) ↥(Γ.edgeOrbitField ε)` with an equally valid head, and the two
collide whenever `i = j`.  It is a `@[reducible] def` promoted by `attribute [local instance]`
inside this section only — `CONVENTIONS.md` §3's rule against ambient instances that can be
silently re-derived, applied before the fact rather than after.

@census none (G4 engine for `RQ2-2.19-C1`)
-/

section EdgeRight

/-- `L(e_ε)` as an `L(v_j)`-algebra, along `edgeComponentRight`.

**Not a global instance, deliberately** — see the section header: `edgeComponentLeft` would give a
competing instance with the same head shape whenever `i = j`.  @census none (helper) -/
@[reducible] noncomputable def edgeRightAlgebra {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) :
    Algebra ↥(Γ.vertexOrbitField j) ↥(Γ.edgeOrbitField ε) :=
  RingHom.toAlgebra (Γ.edgeComponentRight ε).toRingHom

attribute [local instance] edgeRightAlgebra

/-- Membership in `tauEdgeField` is membership in `L(τ_ε⁻¹ e_ε)`, on the nose
(`IntermediateField.mem_extendScalars` is `Iff.rfl`).  Stated so that `rw` has something to fire
on: `extendScalars` is behind the `tauEdgeField` abbreviation and the rewriter cannot see through
it.  @census none (helper) -/
theorem mem_tauEdgeField {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) {x : L} :
    x ∈ tauEdgeField ch ↔ x ∈ stabField K L (ch.τ⁻¹ • Γ.edgeRep ε) := Iff.rfl

/-- **`τ_ε⁻¹ : L(e_ε) ≅ L(τ_ε⁻¹ e_ε)`, as `L(v_j)`-algebras.**

Well-defined in both directions by `stabField_map_smul` (`map_tau_inv_edgeOrbitField` one way, and
`τ_ε (τ_ε⁻¹ • e_ε) = e_ε` the other).  The `commutes'` field is the content: it says
`τ_ε⁻¹(ι_ε b) = b`, which is `edgeComponentRight_coe_tau` — `ι_ε` *is* "apply `τ_ε`" — and it is
the same fact that `twist_edgeComponentRight` packages for the twisted side.

@census none (helper for `RQ2-2.19-C1`) -/
noncomputable def tauEdgeAlgEquiv {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) :
    ↥(Γ.edgeOrbitField ε) ≃ₐ[↥(Γ.vertexOrbitField j)] ↥(tauEdgeField ch) where
  toFun x := ⟨ch.τ⁻¹ (x : L), by
    rw [mem_tauEdgeField, ← map_tau_inv_edgeOrbitField ch, IntermediateField.mem_map]
    exact ⟨(x : L), x.2, rfl⟩⟩
  invFun y := ⟨ch.τ (y : L), by
    have hy : (y : L) ∈ stabField K L (ch.τ⁻¹ • Γ.edgeRep ε) := y.2
    have : ch.τ (y : L) ∈ IntermediateField.map ((ch.τ : Gal(L/K)) : L →ₐ[K] L)
        (stabField K L (ch.τ⁻¹ • Γ.edgeRep ε)) := ⟨(y : L), hy, rfl⟩
    rwa [stabField_map_smul, smul_smul, mul_inv_cancel, one_smul] at this⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' b := Subtype.ext (by
    show ch.τ⁻¹ ((Γ.edgeComponentRight ε b : ↥(Γ.edgeOrbitField ε)) : L) = (b : L)
    rw [edgeComponentRight_coe_tau ch b]
    exact AlgEquiv.symm_apply_apply ch.τ (b : L))

/-- **`eq:Leepsilondecompositionpre` at `L(e_ε)`**: `L ⊗_{L(v_j)} L(e_ε) ≅ ∏_η L`, the `L(v_j)`
acting on `L(e_ε)` through `edgeComponentRight`.

`leEpsilonPreEquiv` transported along `tauEdgeAlgEquiv`.  @census none (helper for `RQ2-2.19-C1`) -/
noncomputable def leEpsilonEquivE {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) [Finite (EdgeChoice.CosetIndex Γ ch)] :
    (L ⊗[↥(Γ.vertexOrbitField j)] ↥(Γ.edgeOrbitField ε)) ≃ₐ[L]
      (EdgeChoice.CosetIndex Γ ch → L) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R := L) (A₁ := L)) (tauEdgeAlgEquiv ch)).trans
    (leEpsilonPreEquiv ch)

/-- The pin: `a ⊗ x ↦ (a · (ητ_ε⁻¹)(x))_η` — the embedding family in the **source's own** spelling
`η ι_ε`, recovered from sub-obligation (3)'s `η(·)` by the transport.

@census none (helper for `RQ2-2.19-C3`) -/
@[simp] theorem leEpsilonEquivE_tmul {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) [Finite (EdgeChoice.CosetIndex Γ ch)]
    (a : L) (x : ↥(Γ.edgeOrbitField ε)) (η : EdgeChoice.CosetIndex Γ ch) :
    leEpsilonEquivE ch (a ⊗ₜ[↥(Γ.vertexOrbitField j)] x) η
      = a * (EdgeChoice.rep Γ ch η * ch.τ⁻¹) (x : L) := by
  show leEpsilonPreEquiv ch (a ⊗ₜ[↥(Γ.vertexOrbitField j)] (tauEdgeAlgEquiv ch x)) η = _
  rw [leEpsilonPreEquiv_tmul, AlgEquiv.mul_apply]
  rfl

/-! ### `RQ2-2.19` sub-obligation (4): the general-`V` assembly

Sub-obligation (3′) splits the *ring*: `L ⊗_{L(v_j)} L(e_ε) ≅ ∏_η L`.  The row is about an
arbitrary `V`, and the source's own argument is "then tensor with `V` over `L(e_ε)`".  That is what
this section does, with two hypotheses spent at two identifiable points: `hV` becomes the scalar
tower `L(v_j) ⊆ L(e_ε)` acting on `V` (`isScalarTower_of_hV`), spent at `cancelBaseChange`; and
`hVT` — the hypothesis finding **S5-F6** forced — is spent at `Twist.rebase`, which is stated with
precisely that shape.

@census none (G4 engine for `RQ2-2.19`)
-/

section Assembly19

variable {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε)
  [Finite (EdgeChoice.CosetIndex Γ ch)]

/-- **The splitting, with the twist conjugated away**: `L(e_ε) ⊗_{L(v_j)} L ≅ ∏_η L`, as
`L(e_ε)`-**modules**.

`leEpsilonEquivE` is `L`-linear and carries `L(e_ε)` to the η-component through `ητ_ε⁻¹`; composing
componentwise with `(ητ_ε⁻¹)⁻¹` conjugates that twist away, leaving the **untwisted** product
`L(e_ε)`-module on the right.  That is what lets the rest of the assembly distribute over the
product with mathlib's `TensorProduct.piRight`, which knows nothing about twists.

The twist is not lost — it is exactly what `Twist.untwist` puts back at the last step, and the two
cancel on the nose (`AlgEquiv.apply_symm_apply` in `leEpsilonChain_tmul`).

@census none (G4 engine for `RQ2-2.19-C1`) -/
noncomputable def splitE :
    (↥(Γ.edgeOrbitField ε) ⊗[↥(Γ.vertexOrbitField j)] L) ≃ₗ[↥(Γ.edgeOrbitField ε)]
      (EdgeChoice.CosetIndex Γ ch → L) := by
  refine AddEquiv.toLinearEquiv
    (((Algebra.TensorProduct.comm ↥(Γ.vertexOrbitField j) ↥(Γ.edgeOrbitField ε) L).toAddEquiv.trans
      (leEpsilonEquivE ch).toAddEquiv).trans
      (AddEquiv.piCongrRight fun η =>
        ((EdgeChoice.rep Γ ch η * ch.τ⁻¹).symm : L ≃ₐ[K] L).toAddEquiv)) ?_
  intro c z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
      funext η
      show ((EdgeChoice.rep Γ ch η * ch.τ⁻¹).symm)
          (leEpsilonEquivE ch (a ⊗ₜ[↥(Γ.vertexOrbitField j)] (c * x)) η)
        = (c : L) * ((EdgeChoice.rep Γ ch η * ch.τ⁻¹).symm)
          (leEpsilonEquivE ch (a ⊗ₜ[↥(Γ.vertexOrbitField j)] x) η)
      rw [leEpsilonEquivE_tmul, leEpsilonEquivE_tmul, map_mul, map_mul,
        AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
      push_cast
      ring
  | add p q hp hq =>
      rw [smul_add, map_add, map_add, hp, hq, smul_add]


@[simp] theorem splitE_tmul (x : ↥(Γ.edgeOrbitField ε)) (a : L)
    (η : EdgeChoice.CosetIndex Γ ch) :
    splitE ch (x ⊗ₜ[↥(Γ.vertexOrbitField j)] a) η
      = (EdgeChoice.rep Γ ch η * ch.τ⁻¹).symm a * (x : L) := by
  show ((EdgeChoice.rep Γ ch η * ch.τ⁻¹).symm)
      (leEpsilonEquivE ch (a ⊗ₜ[↥(Γ.vertexOrbitField j)] x) η) = _
  rw [leEpsilonEquivE_tmul, map_mul, AlgEquiv.symm_apply_apply]

section Assembly

variable (V : Type u) [AddCommGroup V] [Module ↥(Γ.edgeOrbitField ε) V]
    [Module ↥(Γ.vertexOrbitField j) V]
    [∀ τ : Gal(L/K), Module (Twist.TwistBase (Γ.edgeOrbitField ε) τ) V]

/-- **`hV` is a scalar tower.**  The row's hypothesis says the `L(v_j)`-action on `V` factors
through `edgeComponentRight`; that is precisely `IsScalarTower L(v_j) L(e_ε) V`, which is the form
`cancelBaseChange` consumes.  @census none (helper for `RQ2-2.19-C1`) -/
theorem isScalarTower_of_hV
    (hV : ∀ (a : ↥(Γ.vertexOrbitField j)) (v : V),
      a • v = (Γ.edgeComponentRight ε a) • v) :
    IsScalarTower ↥(Γ.vertexOrbitField j) ↥(Γ.edgeOrbitField ε) V where
  smul_assoc b x v := by
    show ((Γ.edgeComponentRight ε b) * x) • v = b • (x • v)
    rw [hV b (x • v), mul_smul]


/-- **`RQ2-2.19` sub-obligation (4): the general-`V` assembly**, as a chain of bijections.

`L ⊗_{L(v_j)} V`
  → `V ⊗_{L(v_j)} L`                       (`comm`)
  → `V ⊗_{L(e_ε)} (L(e_ε) ⊗_{L(v_j)} L)`   (`cancelBaseChange`, backwards — this is where `hV`'s
                                            scalar tower is spent)
  → `V ⊗_{L(e_ε)} (∏_η L)`                 (`splitE` — sub-obligation (3′), conjugated)
  → `∏_η (V ⊗_{L(e_ε)} L)`                 (`piRight`; needs `Finite` of the coset space)
  → `∏_η (L ⊗_{L(e_ε)} V)`                 (`comm`)
  → `∏_η (L ⊗_{TwistBase} V)`              (`Twist.rebase⁻¹` — this is where `hVT` is spent)
  → `∏_η (Twist ⊗_{TwistBase} V)`          (`Twist.untwist⁻¹`, which puts the twist back)

**Only a bijection is built here, deliberately.**  Several links are `L`-semi-linear rather than
`L`-linear — `untwist` is `σ⁻¹`-semi-linear by construction (`untwist_smulL`) — so asking the chain
itself to be `L`-linear would be asking for something false.  `L`-linearity is recovered
afterwards, in `leEpsilonLinearEquiv`, from the **pure-tensor pin** alone: the composite's value on
`a ⊗ v` is `ofL a ⊗ v`, whose `L`-linearity is visible, and both sides are additive.  Splitting the
two concerns is what keeps the semi-linearity bookkeeping out of the statement.

**Why the base ring is `TwistBase` and never `↥E` on the `Twist` side.**  `Module ↥E (Twist E σ)`
resolves to the *untwisted* `SetLike` path, so a `⊗[↥E]` with a `Twist` carrier would silently
assert the untwisted balance — finding **S5-F5** exactly, whose fingerprint the `S5b` pass measured
to zero in this row.  The chain therefore distributes over the product **before** re-introducing
any `Twist`, on the honest untwisted `∏_η L`, and the last two links move to `TwistBase` and
`Twist` together.

@census none (G4 engine for `RQ2-2.19-C1`) -/
noncomputable def leEpsilonChain
    [Fintype (EdgeChoice.CosetIndex Γ ch)] [DecidableEq (EdgeChoice.CosetIndex Γ ch)]
    [IsScalarTower ↥(Γ.vertexOrbitField j) ↥(Γ.edgeOrbitField ε) V]
    (hVT : ∀ (τ : Gal(L/K)) (b : Twist.TwistBase (Γ.edgeOrbitField ε) τ) (v : V),
      b • v = (b.val : ↥(Γ.edgeOrbitField ε)) • v) :
    (L ⊗[↥(Γ.vertexOrbitField j)] V) ≃+
      (∀ η : EdgeChoice.CosetIndex Γ ch,
        Twist (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)
          ⊗[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)] V) :=
  ((TensorProduct.comm ↥(Γ.vertexOrbitField j) L V).toAddEquiv.trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange
        ↥(Γ.vertexOrbitField j) ↥(Γ.edgeOrbitField ε) ↥(Γ.edgeOrbitField ε) V L).symm.toAddEquiv.trans
      ((TensorProduct.congr (LinearEquiv.refl ↥(Γ.edgeOrbitField ε) V)
          (splitE ch)).toAddEquiv.trans
        ((TensorProduct.piRight ↥(Γ.edgeOrbitField ε) ↥(Γ.edgeOrbitField ε) V
            (fun _ : EdgeChoice.CosetIndex Γ ch => L)).toAddEquiv.trans
          (AddEquiv.piCongrRight fun η =>
            ((TensorProduct.comm ↥(Γ.edgeOrbitField ε) V L).toAddEquiv.trans
              ((Twist.rebase (E := Γ.edgeOrbitField ε)
                  (σ := EdgeChoice.rep Γ ch η * ch.τ⁻¹) V (hVT _)).symm.trans
                (TensorProduct.congr
                  (Twist.untwist (E := Γ.edgeOrbitField ε)
                    (σ := EdgeChoice.rep Γ ch η * ch.τ⁻¹)).symm
                  (LinearEquiv.refl _ V)).toAddEquiv)))))))


/-- `Twist.rebase`'s inverse on a pure tensor, which is `rfl`.  Stated because `rw` cannot see
through the `AddEquiv.symm` of a structure literal.  @census none (helper) -/
theorem rebase_symm_tmul {σ : Gal(L/K)}
    (hW : ∀ (b : Twist.TwistBase (Γ.edgeOrbitField ε) σ) (w : V),
      b • w = (b.val : ↥(Γ.edgeOrbitField ε)) • w) (a : L) (w : V) :
    (Twist.rebase (E := Γ.edgeOrbitField ε) (σ := σ) V hW).symm
        (a ⊗ₜ[↥(Γ.edgeOrbitField ε)] w)
      = a ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) σ] w := rfl

/-- **The pin**: the chain sends `a ⊗ v` to the constant family `(ofL a ⊗ v)_η` — clause
`RQ2-2.19-C3`.

Traced link by link; every step but two is `rfl`, and the two that are not are `splitE_tmul` and
`piRightHom_tmul`.  The `ρ_η⁻¹` that `splitE` introduced and the `ρ_η` that `untwist⁻¹` puts back
cancel by `AlgEquiv.apply_symm_apply`, which is the sense in which the twist is bookkeeping in the
middle of the chain and real only at its ends.

*A `CONVENTIONS.md` §3 (i) instance, for the record.*  `rw` could not fire on any link: after
`AddEquiv.trans_apply` the terms sit under a coercion and the printed goal shows `↑(...)` where the
lemmas expect the bare application, so every rewrite reported "pattern not found" and the failure
looked like missing lemmas.  The fix is the documented one — **pin the shape with `show` first**,
in the coercion-free spelling — after which the same rewrites all fire.  No instance was missing
and no construction needed changing.

@census none (clause witness for `RQ2-2.19-C3`) -/
theorem leEpsilonChain_tmul
    [Fintype (EdgeChoice.CosetIndex Γ ch)] [DecidableEq (EdgeChoice.CosetIndex Γ ch)]
    [IsScalarTower ↥(Γ.vertexOrbitField j) ↥(Γ.edgeOrbitField ε) V]
    (hVT : ∀ (τ : Gal(L/K)) (b : Twist.TwistBase (Γ.edgeOrbitField ε) τ) (v : V),
      b • v = (b.val : ↥(Γ.edgeOrbitField ε)) • v)
    (a : L) (v : V) (η : EdgeChoice.CosetIndex Γ ch) :
    leEpsilonChain ch V hVT (a ⊗ₜ[↥(Γ.vertexOrbitField j)] v) η
      = Twist.ofL a
          ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)] v := by
  show (TensorProduct.congr (Twist.untwist (E := Γ.edgeOrbitField ε)
        (σ := EdgeChoice.rep Γ ch η * ch.τ⁻¹)).symm
      (LinearEquiv.refl (Twist.TwistBase (Γ.edgeOrbitField ε)
        (EdgeChoice.rep Γ ch η * ch.τ⁻¹)) V))
      ((Twist.rebase (E := Γ.edgeOrbitField ε)
          (σ := EdgeChoice.rep Γ ch η * ch.τ⁻¹) V (hVT _)).symm
        ((TensorProduct.comm ↥(Γ.edgeOrbitField ε) V L)
          ((TensorProduct.piRight ↥(Γ.edgeOrbitField ε) ↥(Γ.edgeOrbitField ε) V
              (fun _ : EdgeChoice.CosetIndex Γ ch => L))
            ((TensorProduct.congr (LinearEquiv.refl ↥(Γ.edgeOrbitField ε) V) (splitE ch))
              ((TensorProduct.AlgebraTensorModule.cancelBaseChange ↥(Γ.vertexOrbitField j)
                  ↥(Γ.edgeOrbitField ε) ↥(Γ.edgeOrbitField ε) V L).symm
                ((TensorProduct.comm ↥(Γ.vertexOrbitField j) L V)
                  (a ⊗ₜ[↥(Γ.vertexOrbitField j)] v)))) η))) = _
  have h1 : (TensorProduct.AlgebraTensorModule.cancelBaseChange ↥(Γ.vertexOrbitField j)
        ↥(Γ.edgeOrbitField ε) ↥(Γ.edgeOrbitField ε) V L).symm
      ((TensorProduct.comm ↥(Γ.vertexOrbitField j) L V) (a ⊗ₜ[↥(Γ.vertexOrbitField j)] v))
      = v ⊗ₜ[↥(Γ.edgeOrbitField ε)] ((1 : ↥(Γ.edgeOrbitField ε))
          ⊗ₜ[↥(Γ.vertexOrbitField j)] a) := rfl
  rw [h1]
  have h2 : (TensorProduct.congr (LinearEquiv.refl ↥(Γ.edgeOrbitField ε) V) (splitE ch))
      (v ⊗ₜ[↥(Γ.edgeOrbitField ε)] ((1 : ↥(Γ.edgeOrbitField ε))
        ⊗ₜ[↥(Γ.vertexOrbitField j)] a))
      = v ⊗ₜ[↥(Γ.edgeOrbitField ε)]
          (splitE ch ((1 : ↥(Γ.edgeOrbitField ε)) ⊗ₜ[↥(Γ.vertexOrbitField j)] a)) := rfl
  rw [h2, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  have h3 : (TensorProduct.comm ↥(Γ.edgeOrbitField ε) V L)
      (v ⊗ₜ[↥(Γ.edgeOrbitField ε)]
        (splitE ch ((1 : ↥(Γ.edgeOrbitField ε)) ⊗ₜ[↥(Γ.vertexOrbitField j)] a) η))
      = (splitE ch ((1 : ↥(Γ.edgeOrbitField ε)) ⊗ₜ[↥(Γ.vertexOrbitField j)] a) η)
          ⊗ₜ[↥(Γ.edgeOrbitField ε)] v := rfl
  rw [h3, splitE_tmul, OneMemClass.coe_one, mul_one, rebase_symm_tmul]
  have h4 : (TensorProduct.congr (Twist.untwist (E := Γ.edgeOrbitField ε)
        (σ := EdgeChoice.rep Γ ch η * ch.τ⁻¹)).symm
      (LinearEquiv.refl (Twist.TwistBase (Γ.edgeOrbitField ε)
        (EdgeChoice.rep Γ ch η * ch.τ⁻¹)) V))
      (((EdgeChoice.rep Γ ch η * ch.τ⁻¹).symm a)
        ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)] v)
      = Twist.ofL ((EdgeChoice.rep Γ ch η * ch.τ⁻¹) ((EdgeChoice.rep Γ ch η * ch.τ⁻¹).symm a))
        ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)] v := rfl
  rw [h4, AlgEquiv.apply_symm_apply]


/-- **The chain, upgraded to an `L`-linear equivalence** — clause `RQ2-2.19-C1`.

`L`-linearity is proved from the pin, not from the links: on `a ⊗ v` both sides are
`ofL (c·a) ⊗ v`, and `TensorProduct.induction_on` extends that over sums.  This is why the chain
was built as an `AddEquiv`: the individual links are not `L`-linear, and the composite is.

@census none (clause witness for `RQ2-2.19-C1`) -/
noncomputable def leEpsilonLinearEquiv
    [Fintype (EdgeChoice.CosetIndex Γ ch)] [DecidableEq (EdgeChoice.CosetIndex Γ ch)]
    [IsScalarTower ↥(Γ.vertexOrbitField j) ↥(Γ.edgeOrbitField ε) V]
    (hVT : ∀ (τ : Gal(L/K)) (b : Twist.TwistBase (Γ.edgeOrbitField ε) τ) (v : V),
      b • v = (b.val : ↥(Γ.edgeOrbitField ε)) • v) :
    (L ⊗[↥(Γ.vertexOrbitField j)] V) ≃ₗ[L]
      (∀ η : EdgeChoice.CosetIndex Γ ch,
        Twist (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)
          ⊗[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)] V) := by
  refine AddEquiv.toLinearEquiv (leEpsilonChain ch V hVT) ?_
  intro c z
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul a v =>
      funext η
      show leEpsilonChain ch V hVT ((c * a) ⊗ₜ[↥(Γ.vertexOrbitField j)] v) η
        = c • (leEpsilonChain ch V hVT (a ⊗ₜ[↥(Γ.vertexOrbitField j)] v) η)
      rw [leEpsilonChain_tmul, leEpsilonChain_tmul]
      show Twist.ofL (c * a) ⊗ₜ _ = (c • Twist.ofL a) ⊗ₜ _
      rfl
  | add p q hp hq => rw [smul_add, map_add, map_add, hp, hq, smul_add]

end Assembly

end Assembly19

/-! ### `RQ2-2.19` — the row, RELOCATED (coordinator ruling, `DESIGN-NOTES` §49)

The statement stood at line 198, above **all twelve** of its own ingredients; Lean has no forward
references, so its `sorry` could not be discharged where it was.  It is moved here — after
`leEpsilonPreEquiv_tmul`, the last of them — under `variable (Γ) in`, so that `Γ` stays **explicit**
and the elaborated signature differs from §49’s recorded pre-move `#check` by exactly the one
hypothesis §48 forced (`hVT`) and by nothing else.  That diff **is** the relocation’s certificate.

`compactSpace_stabilizer_V` and `finite_cosetIndex` move with it, from the `RQ2-2.23-C6` section
below: they are `@census none` helpers, they keep their own `@clauses RQ2-2.23-C6` docstrings, and
the row’s proof needs the finiteness.  `wiiMj_baseChange_pre` does not move.

@census none (relocation banner)
-/

/-- `G_v` is compact: closed in the profinite `Gal(L/K)`.  @census none (helper) -/
instance compactSpace_stabilizer_V (v : Γ.V) :
    CompactSpace ↥(stabilizer Gal(L/K) v) :=
  isCompact_iff_compactSpace.mp (IsClosed.isCompact (Γ.isClosed_stabilizer_V v))

/-- **Clause `RQ2-2.23-C6`, finiteness.**  @census none (clause witness)
@clauses   RQ2-2.23-C6 -/
theorem finite_cosetIndex {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) : Finite (EdgeChoice.CosetIndex Γ ch) :=
  Subgroup.quotient_finite_of_isOpen _
    (Subgroup.subgroupOf_isOpen _ _ (Γ.isOpen_stabilizer_E _))

variable (Γ) in
/-- **Proposition** (`unlabeled:2`, census `RQ2-2.19`).

For **any** right `L(e_ε)`-vector space `V` (clause `RQ2-2.19-H1`) there is a canonical isomorphism
of `L`-vector spaces

`V ⊗_{τ_ε, L(v_j)} L  ≅  ∏_{η ∈ G_{v_j}/G_{τ_ε^{-1}e_ε}} V ⊗_{L(e_ε), η τ_ε^{-1}} L`
  (`eq:Leepsilondecomposition`, clause `RQ2-2.19-C1`),

the index set being the coset space of clause `RQ2-2.19-C2`, and on pure tensors the isomorphism is
`v ⊗ a ↦ (v ⊗ a)_η` (clause `RQ2-2.19-C3`) — the last conjunct below, which is what the proof of
`RQ2-2.23` consumes.

@census    RQ2-2.19
@source    prop:ledecomposition
@clauses   RQ2-2.19-H1, RQ2-2.19-H2, RQ2-2.19-Hs1, RQ2-2.19-C1, RQ2-2.19-C2, RQ2-2.19-C3
@imports   none
@divergence JUSTIFIED_REFORMULATION on clause `RQ2-2.19-C1`, on two presentational points, neither
touching the content.

*Factor order.* Both tensor products are written with the field on the left, mathlib's order for a
base change; the source writes `V ⊗ L`. The objects are the same and no clause depends on the
order — the same disclosure `Species/Rep/Tensor.lean` carries.

*Where each twist sits.* Per `census/NOTATION.md` §2, `⊗_{L(e_ε), η τ_ε^{-1}} L` names the twist
**after** the ring, so it is on the `L` side: that is `Twist (L(e_ε)) (η τ_ε⁻¹)`, an honest wrapper
whose `smul_def` keeps the twist visible in the signature (finding **S5-F4**). The mirror
`⊗_{τ_ε, L(v_j)}` names it **before** the ring, so it is on `V`'s side; since `V` is an arbitrary
space (clause `H1`) that structure is *given*, and it is carried as the explicit hypothesis `hV`
rather than by a second wrapper. `hV` is the whole of the mirror twist and is visible in the
statement.

*Canonicity* (clause `C1`'s "canonical") is delivered by clause `C3`: the isomorphism is not merely
asserted to exist, it is pinned by its value on pure tensors, which determines it.

*The `hVT` hypothesis* (finding **S5-F6**, `DESIGN-NOTES` §48; coordinator-sanctioned delta).  An
**implementation artifact, not source mathematics**, and the census is untouched.  The `S5-F5`
repair respelled the conclusion's tensor base as `Twist.TwistBase (L(e_ε)) τ` and gave `V` the
matching instance binder; nothing then said what that action *is*, so it was a free parameter of the
statement while being exactly the action the conclusion is balanced over.  `hVT` says the respelled
base acts through `TwistBase.toE` — the untwisted reading the module side is *supposed* to have,
which `Rep.moduleTwistBase_vertexFixed` (`Module.compHom _ TwistBase.toE`) satisfies by `rfl`, so
`RQ2-2.20`, the only consumer, pays nothing.

It is a **disclosure, not a weakening**: `leEpsilon_decomposition_entails_untwisted_base` proves,
`sorry`-free, that this row's own conclusion *entails* `hVT`.  Any proof of the row proves it; the
statement asserted it either way, and the hypothesis only makes it visible.  That entailment is the
fidelity certificate for leaving the census alone.

Proof plan (G4), the source's own: `L(e_ε) ⊗_{τ_ε,L(v_j)} L = ∏_{τ} L(e_ε) ⊗_{L(e_ε),ττ_ε^{-1}} L`
over the `L(v_j)`-linear embeddings `τ : L(τ_ε^{-1}e_ε) → L`
(`eq:Leepsilondecompositionpre`), each of which is `η ι_ε` for a unique coset
`η G_{τ_ε^{-1}e_ε} ∈ G_{v_j}/G_{τ_ε^{-1}e_ε}`; then tensor with `V` over `L(e_ε)`. The counting
step is Galois theory for `L/K` and is where clause `Hs1` is load-bearing.
-/
theorem leEpsilon_decomposition {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε)
    (V : Type u) [AddCommGroup V] [Module ↥(Γ.edgeOrbitField ε) V]
    [Module ↥(Γ.vertexOrbitField j) V]
    [∀ τ : Gal(L/K), Module (Twist.TwistBase (Γ.edgeOrbitField ε) τ) V]
    (hV : ∀ (a : ↥(Γ.vertexOrbitField j)) (v : V),
      a • v = (Γ.edgeComponentRight ε a) • v)
    (hVT : ∀ (τ : Gal(L/K)) (b : Twist.TwistBase (Γ.edgeOrbitField ε) τ) (v : V),
      b • v = (b.val : ↥(Γ.edgeOrbitField ε)) • v) :
    ∃ e : (L ⊗[↥(Γ.vertexOrbitField j)] V) ≃ₗ[L]
        (∀ η : EdgeChoice.CosetIndex Γ ch,
          Twist (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)
            ⊗[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)] V),
      ∀ (a : L) (v : V) (η : EdgeChoice.CosetIndex Γ ch),
        e (a ⊗ₜ[↥(Γ.vertexOrbitField j)] v) η
          = Twist.ofL a
              ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)] v := by
  classical
  haveI : Finite (EdgeChoice.CosetIndex Γ ch) := finite_cosetIndex ch
  letI : Fintype (EdgeChoice.CosetIndex Γ ch) := Fintype.ofFinite _
  haveI := isScalarTower_of_hV V hV
  exact ⟨leEpsilonLinearEquiv ch V hVT, fun a v η => leEpsilonChain_tmul ch V hVT a v η⟩

end EdgeRight

/-! ### Continuity of `Gal(L/E) → Gal(L/K)` for the Krull topologies

To move the open-stabilizer condition from `Gal(L/K)` down to `Gal(L/L(v))` we need the
restriction map `σ ↦ σ|_K` to be **continuous**.  Mathlib does not have this: it has the Krull
topology on each Galois group and the *algebraic* isomorphism
`IntermediateField.fixingSubgroupEquiv : E.fixingSubgroup ≃* Gal(L/E)`, but nothing topological
relating the two — the statement below is one half of that missing homeomorphism.  So we prove it.

The argument is the standard one, and is the model mathlib itself uses for
`AlgEquiv.restrictNormalHom_continuous`: reduce to continuity at `1`; a basic neighbourhood of `1`
in `Gal(L/K)` contains `F^fix` for some *finite* `F/K`; pick a finite `K`-spanning set `S` of `F`;
then `(E(S))^fix` is a basic neighbourhood of `1` in `Gal(L/E)` — finite over `E` because each
element of `S` is integral over `K`, hence over `E` — and any `τ` fixing `S` fixes all `K`-linear
combinations of `S`, i.e. all of `F`.

Recorded as an **UPSTREAM-CANDIDATE** (`MD-S5-04`): it is stated purely in mathlib's vocabulary,
mentions nothing of this development, and is exactly the lemma mathlib is missing.

@census none (helpers for `RQ2-2.21`)
-/

section KrullContinuity

/-- `σ ↦ σ|_K`, as a monoid homomorphism `Gal(L/E) →* Gal(L/K)`.

Mathlib has `AlgEquiv.restrictScalars` as a bare function only; the bundled form is what
`continuous_of_continuousAt_one` needs.  @census none (helper) -/
def restrictScalarsHom (E : IntermediateField K L) : Gal(L/↥E) →* Gal(L/K) :=
  E.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom

@[simp]
theorem restrictScalarsHom_apply (E : IntermediateField K L) (σ : Gal(L/↥E)) :
    restrictScalarsHom E σ = σ.restrictScalars K := rfl

/-- A finite-dimensional intermediate field is fixed as soon as a finite spanning set of it is.

This is the step that turns "finite over `K`" into a *finite* condition, and it is where the
`K`-linearity of a `K`-algebra automorphism is used.  @census none (helper) -/
theorem exists_finite_fixing_set (F : IntermediateField K L) [FiniteDimensional K F] :
    ∃ S : Set L, S.Finite ∧
      ∀ τ : Gal(L/K), (∀ x ∈ S, τ x = x) → ∀ x ∈ F, τ x = x := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite K ↥F).fg_top
  refine ⟨(fun x : ↥F => (x : L)) '' s, s.finite_toSet.image _, ?_⟩
  intro τ hτ x hx
  suffices h : ∀ y ∈ Submodule.span K (s : Set ↥F), τ (y : L) = (y : L) by
    exact h ⟨x, hx⟩ (hs ▸ Submodule.mem_top)
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact hτ _ ⟨y, hy, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => push_cast; rw [map_add, ha, hb]
  | smul c a _ ha =>
      show τ ((c • a : ↥F) : L) = ((c • a : ↥F) : L)
      rw [show ((c • a : ↥F) : L) = algebraMap K L c * (a : L) from by
        simp [Algebra.smul_def]]
      rw [map_mul, AlgEquiv.commutes, ha]

open scoped Topology in
/-- **Restriction of scalars is continuous for the Krull topologies.**

`Gal(L/E) → Gal(L/K)`, `σ ↦ σ|_K`, is continuous.  Mathlib lacks this (`MD-S5-04`,
UPSTREAM-CANDIDATE); see the section note for the argument.

@census none (helper for `RQ2-2.21`)
-/
theorem continuous_restrictScalarsHom (E : IntermediateField K L) :
    Continuous (restrictScalarsHom E) := by
  apply continuous_of_continuousAt_one
  rw [continuousAt_def, map_one]
  intro N hN
  rw [krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨F, hFfin, hFsub⟩ := hN
  obtain ⟨S, hSfin, hSfix⟩ := exists_finite_fixing_set F
  rw [krullTopology_mem_nhds_one_iff]
  haveI : Finite S := hSfin.to_subtype
  refine ⟨IntermediateField.adjoin ↥E S, ?_, ?_⟩
  · refine IntermediateField.finiteDimensional_adjoin (fun x _ => ?_)
    exact (Algebra.IsIntegral.isIntegral (R := K) x).tower_top
  · intro τ hτ
    apply hFsub
    show restrictScalarsHom E τ ∈ F.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    refine hSfix (restrictScalarsHom E τ) (fun x hx => ?_)
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x
      (IntermediateField.subset_adjoin _ _ hx)

end KrullContinuity

/-! ### `M(v)` as an object of `VecK L(v) L`

With `G_v = Gal(L/L(v))` identified, `M(v)` is an `L`-vector space carrying a continuous
semi-linear `Gal(L/L(v))`-action — i.e. an object of stage S0's `Descent.VecK L(v) L`, the very
category `RQ2-1.13` is about.  Feeding it to `Descent.descentCounit_bijective` is `RQ2-2.21-C4`.

@census none (helpers for `RQ2-2.21`)
-/

section VertexVecK

variable (M : Rep Γ) (v : Γ.V)

/-- `M(v)` as an `L(v)`-vector space, by restriction along `L(v) ↪ L`.  @census none (helper) -/
noncomputable instance Rep.moduleStabField : Module ↥(stabField K L v) (M.M v) :=
  Module.compHom _ (algebraMap ↥(stabField K L v) L)

/-- The `L(v)`-structure on `M(v)` is the induced one.  @census none (helper) -/
instance Rep.tower_stabField : IsScalarTower ↥(stabField K L v) L (M.M v) where
  smul_assoc c a x := by
    show ((c : L) * a) • x = (c : L) • (a • x)
    rw [mul_smul]

/-- The `Gal(L/L(v))`-action on `M(v)`, transported from the `G_v`-action along the correspondence.
@census none (helper) -/
noncomputable instance Rep.galStabFieldAction :
    DistribMulAction Gal(L/↥(stabField K L v)) (M.M v) where
  smul σ m := (Γ.galStabFieldEquiv v σ) • m
  one_smul m := by
    show (Γ.galStabFieldEquiv v 1) • m = m
    rw [map_one, one_smul]
  mul_smul σ τ m := by
    show (Γ.galStabFieldEquiv v (σ * τ)) • m
        = (Γ.galStabFieldEquiv v σ) • ((Γ.galStabFieldEquiv v τ) • m)
    rw [map_mul, mul_smul]
  smul_zero σ := smul_zero (Γ.galStabFieldEquiv v σ)
  smul_add σ a b := smul_add (Γ.galStabFieldEquiv v σ) a b

theorem Rep.galStabFieldAction_smul (σ : Gal(L/↥(stabField K L v))) (m : M.M v) :
    σ • m = M.φ' (σ.restrictScalars K) (Γ.galStabFieldEquiv v σ).2 m := rfl

/-- `M(v)` is a `K`-structure over `L(v)`: semi-linear, and continuous in open-stabilizer form.

Semi-linearity is `φ'_smul`.  Continuity is the fibrewise condition extracted from `RQ2-1.08-C6`,
pulled back along the correspondence — and pulling an open set back along
`AlgEquiv.restrictScalars` is continuous because the correspondence is a homeomorphism onto the
open subgroup `G_v`, which is how the Krull topologies of `Gal(L/K)` and `Gal(L/L(v))` are related.

@census none (helper for `RQ2-2.21`)
-/
instance Rep.kStructure_vertex : Descent.KStructure ↥(stabField K L v) L (M.M v) where
  smul_smul_semilinear σ a m := M.φ'_smul _ _ a m
  isOpen_stabilizer m := by
    have hpre : ((MulAction.stabilizer Gal(L/↥(stabField K L v)) m : Subgroup _) : Set _)
        = restrictScalarsHom (stabField K L v) ⁻¹'
            {σ : Gal(L/K) | ∃ h : σ • v = v, M.φ' σ h m = m} := by
      ext τ
      simp only [Set.mem_preimage, Set.mem_setOf_eq, SetLike.mem_coe,
        MulAction.mem_stabilizer_iff]
      constructor
      · intro h
        exact ⟨(Γ.galStabFieldEquiv v τ).2, h⟩
      · rintro ⟨_, h⟩
        exact h
    rw [hpre]
    exact (continuous_restrictScalarsHom (stabField K L v)).isOpen_preimage _
      (M.isOpen_fibre_stabilizer v m)

/-- `M(v)` as an object of `VecK L(v) L`.  @census none (helper for `RQ2-2.21`) -/
noncomputable def Rep.vertexVecK : Descent.VecK ↥(stabField K L v) L where
  carrier := M.M v
  isAddCommGroup := inferInstance
  isModuleK := M.moduleStabField v
  isModuleL := inferInstance
  isScalarTower := M.tower_stabField v
  galoisAction := M.galStabFieldAction v
  isKStructure := M.kStructure_vertex v

/-- The two actions on `M(v)` agree under the correspondence.  @census none (helper) -/
theorem Rep.galStabFieldAction_smul' (σ : stabilizer Gal(L/K) v) (m : M.M v) :
    (Γ.galStabFieldEquiv v).symm σ • m = σ • m := by
  rw [Rep.galStabFieldAction_smul, Rep.vertexMulAction_smul]
  exact M.φ'_congr
    (congrArg (fun t : stabilizer Gal(L/K) v => (t : Gal(L/K)))
      ((Γ.galStabFieldEquiv v).apply_symm_apply σ)) _ _ m

/-- `RQ2-2.21-C1`, in descent form: the fixed points of `M(v)` in `VecK L(v) L` are `W_v`.

@census none (helper for `RQ2-2.21`)
@clauses   RQ2-2.21-C1
-/
theorem Rep.fixedPoints_vertexVecK :
    Descent.fixedPoints ↥(stabField K L v) L (Rep.vertexVecK M v)
      = M.vertexFixed v := by
  ext m
  simp only [Descent.mem_fixedPoints]
  show (∀ σ : Gal(L/↥(stabField K L v)), σ • m = m) ↔ _
  constructor
  · intro h σ
    exact (M.galStabFieldAction_smul' v σ m).symm.trans (h ((Γ.galStabFieldEquiv v).symm σ))
  · intro h σ
    have hs : (Γ.galStabFieldEquiv v).symm (Γ.galStabFieldEquiv v σ) • m = m :=
      (M.galStabFieldAction_smul' v (Γ.galStabFieldEquiv v σ) m).trans
        (h (Γ.galStabFieldEquiv v σ))
    rwa [(Γ.galStabFieldEquiv v).symm_apply_apply] at hs

end VertexVecK

/-! ### The scalar structures `W_v` needs to enter a `⊗`

`M(v)` is an `L`-vector space and nothing more: mathlib deliberately has **no** global instance
producing `Module K X` from `[Algebra K L] [Module L X]`, which stage S2 measured and recorded as
`MD-S2-03` (and solved on its own side by packaging `Hom` as an `S0` `VecK`). `W_v` therefore has
to be given its ambient `K`-structure, and its *right* `L(v)`-structure, explicitly before it can
sit inside a balanced tensor product.

All three below are the corresponding projection composed with an algebra map — no new path, so the
`rfl`-identity guarantee of §11.3 applies to them as it does to the étale-side layer.  `L(v)` is
commutative, so the right action is the left one read through `RingEquiv.toOpposite`, exactly as S3
defines `EtaleSpecies.moduleRight`.
-/

/-- `W_v`'s ambient `K`-structure, through `L(v)`.  @census none (helper) -/
noncomputable instance Rep.moduleK_vertexFixed (M : Rep Γ) (v : Γ.V) :
    Module K ↥(M.vertexFixed v) :=
  Module.compHom _ (algebraMap K ↥(stabField K L v))

/-- `W_v` as a **right** `L(v)`-vector space, which is the side `RQ2-2.17` puts `W_i` on.
@census none (helper) -/
noncomputable instance Rep.moduleOp_vertexFixed (M : Rep Γ) (v : Γ.V) :
    Module (↥(stabField K L v))ᵐᵒᵖ ↥(M.vertexFixed v) :=
  Module.compHom _ ((RingEquiv.toOpposite ↥(stabField K L v)).symm.toRingHom)

/-- `W_v`'s `K`-structure is the induced one — `Species/Rep/Tensor.lean`'s standing assumption (3),
without which `W_v ⊗_{L(v)} −` would be a proper quotient of the balanced tensor product
(verification finding **V-S5a-2**).

@census none (helper)
-/
instance Rep.tower_vertexFixed (M : Rep Γ) (v : Γ.V) :
    IsScalarTower K (↥(stabField K L v))ᵐᵒᵖ ↥(M.vertexFixed v) where
  smul_assoc c b x := by
    show (MulOpposite.unop (c • b)) • x
        = (algebraMap K ↥(stabField K L v) c) • (MulOpposite.unop b • x)
    rw [← mul_smul]
    congr 1
    rw [Algebra.smul_def]
    show MulOpposite.unop b * algebraMap K ↥(stabField K L v) c
        = algebraMap K ↥(stabField K L v) c * MulOpposite.unop b
    exact mul_comm _ _

/-! ### `W_i` at the species head

`Γ.toSpecies.L i` and `stabField K L (Γ.vertexRep i)` are the same field — `toSpecies` sets
`L := Γ.vertexOrbitField` and `vertexOrbitField i := stabField K L (vertexRep i)` — but instance
search does not identify them.  This is the third crossing of the boundary finding **S5-F3**
records, and `DESIGN-NOTES` §12's rule predicts it: *expect to pay this once per boundary crossed*.
Three bridges, each literally the instance it re-heads.

@census none (helpers, S5-F3 pattern)
-/

/-- `W_i` as a right `L_i`-space, at the species head.  @census none (helper) -/
noncomputable instance Rep.moduleOp_W (M : Rep Γ) (i : Γ.VertexOrbit) :
    Module (Γ.toSpecies.L i)ᵐᵒᵖ ↥(M.vertexFixed (Γ.vertexRep i)) :=
  M.moduleOp_vertexFixed (Γ.vertexRep i)

/-- `W_i`'s ambient `K`-structure, at the species head.  @census none (helper) -/
noncomputable instance Rep.moduleK_W (M : Rep Γ) (i : Γ.VertexOrbit) :
    Module K ↥(M.vertexFixed (Γ.vertexRep i)) :=
  M.moduleK_vertexFixed (Γ.vertexRep i)

/-- The `K`-structure of `W_i` is the induced one, at the species head.  @census none (helper) -/
instance Rep.tower_W (M : Rep Γ) (i : Γ.VertexOrbit) :
    IsScalarTower K (Γ.toSpecies.L i)ᵐᵒᵖ ↥(M.vertexFixed (Γ.vertexRep i)) :=
  M.tower_vertexFixed (Γ.vertexRep i)

/-! ### `RQ2-2.21`'s extension map, constructed  (G4)

The source's `m ⊗ a ↦ φ_{v,σ}(m)·a`, built directly.  Writing it as a `TensorProduct.liftAddHom`
over the respelled base makes the **balance condition** the whole content, and that condition is
exactly where the twist earns its keep:

  `f (b · x) m = σ(b)·x · φ'_σ(m)`   and   `f x (b · m) = x · φ'_σ(b·m) = x · σ(b) · φ'_σ(m)`,

equal because `L` is commutative.  Under the *untwisted* base action the left side would be
`b·x·φ'_σ(m)` and the two would differ unless `σ` fixed `L(v)` — which is finding **S5-F5** seen
from the proof side rather than the statement side.

@census none (G4 engine for `RQ2-2.21`)
-/

/-- `a ⊗ m ↦ a · φ'_{v,σ}(m)`, in the second argument.  @census none (helper) -/
noncomputable def generalExtensionAux (M : Rep Γ) (v : Γ.V) (σ : Gal(L/K))
    (x : Twist (stabField K L v) σ) : ↥(M.vertexFixed v) →+ M.M (σ • v) where
  toFun m := x.val • M.φ' σ rfl (m : M.M v)
  map_zero' := by
    show x.val • M.φ' σ rfl (0 : M.M v) = 0
    rw [map_zero, smul_zero]
  map_add' a b := by
    show x.val • M.φ' σ rfl ((a : M.M v) + (b : M.M v)) = _
    rw [map_add, smul_add]

/-- The same, additive in the first argument too.  @census none (helper) -/
noncomputable def generalExtensionBil (M : Rep Γ) (v : Γ.V) (σ : Gal(L/K)) :
    Twist (stabField K L v) σ →+ (↥(M.vertexFixed v) →+ M.M (σ • v)) where
  toFun := generalExtensionAux M v σ
  map_zero' := by
    ext m
    show (0 : Twist (stabField K L v) σ).val • M.φ' σ rfl (m : M.M v) = 0
    rw [Twist.val_zero, zero_smul]
  map_add' x y := by
    ext m
    show (x + y).val • M.φ' σ rfl (m : M.M v)
      = x.val • M.φ' σ rfl (m : M.M v) + y.val • M.φ' σ rfl (m : M.M v)
    rw [Twist.val_add, add_smul]

/-- The map of `eq:generalextensionisomorphism`: `a ⊗ m ↦ a · φ'_{v,σ}(m)`.
@census none (helper for `RQ2-2.21-C2`) -/
noncomputable def generalExtensionMap (M : Rep Γ) (v : Γ.V) (σ : Gal(L/K)) :
    (Twist (stabField K L v) σ
        ⊗[Twist.TwistBase (stabField K L v) σ] ↥(M.vertexFixed v)) →+ M.M (σ • v) :=
  TensorProduct.liftAddHom (generalExtensionBil M v σ)
    (by
      intro b x m
      show (b • x).val • M.φ' σ rfl ((m : M.M v))
        = x.val • M.φ' σ rfl (((b • m : ↥(M.vertexFixed v)) : M.M v))
      have hb : ((b • m : ↥(M.vertexFixed v)) : M.M v)
          = ((b.val : ↥(stabField K L v)) : L) • (m : M.M v) := rfl
      rw [hb, M.φ'_smul, Twist.val_smulL_base, smul_smul, mul_comm])

@[simp]
theorem generalExtensionMap_tmul (M : Rep Γ) (v : Γ.V) (σ : Gal(L/K)) (a : L)
    (m : ↥(M.vertexFixed v)) :
    generalExtensionMap M v σ (Twist.ofL a ⊗ₜ m) = a • M.φ σ v (m : M.M v) := rfl

/-- Stage S0's Galois descent at `L / L(v)`, in the form `RQ2-2.21` consumes:
the canonical map `L ⊗_{L(v)} W_v → M(v)`, `a ⊗ m ↦ a · m`.

Written as the same `liftBaseChange` that `Descent.descentCounit` is, so that the bijectivity
transport below is a rewrite along one submodule equality and nothing more.

@census none (helper for `RQ2-2.21-C4`) -/
noncomputable def vertexDescentMap (M : Rep Γ) (v : Γ.V) :
    (L ⊗[↥(stabField K L v)] ↥(M.vertexFixed v)) →ₗ[L] M.M v :=
  LinearMap.liftBaseChange L ((M.vertexFixed v).subtype)

@[simp]
theorem vertexDescentMap_tmul (M : Rep Γ) (v : Γ.V) (a : L) (m : ↥(M.vertexFixed v)) :
    vertexDescentMap M v (a ⊗ₜ m) = a • (m : M.M v) := rfl

/-- The tensor factor transported along `fixedPoints = W_v`.  A `def`, not a `have`: a `have`
would make it opaque and the pure-tensor step below could not reduce.  @census none (helper) -/
noncomputable def vertexFixedTransport (M : Rep Γ) (v : Γ.V) :
    (L ⊗[↥(stabField K L v)] ↥(M.vertexFixed v)) ≃ₗ[↥(stabField K L v)]
      (L ⊗[↥(stabField K L v)] ↥(Descent.fixedPoints ↥(stabField K L v) L
        (Rep.vertexVecK M v))) :=
  TensorProduct.congr (LinearEquiv.refl _ _)
    (LinearEquiv.ofEq _ _ (M.fixedPoints_vertexVecK v).symm)

/-- **`RQ2-1.13` at `L / L(v)`** — design decision `D1`'s payoff, and the reason
`Rep.vertexVecK` had to be made unconditional (`MD-S5-04`).

`vertexDescentMap` and `Descent.descentCounit` are the *same* map — both are
`liftBaseChange` of the inclusion, and they agree on pure tensors by `rfl`
(`vertexFixedTransport` moves between the two spellings of the fixed submodule). So bijectivity
transfers from `Descent.descentCounit_bijective`.

**Remaining obligation, and it is plumbing, not mathematics.** Transferring it needs the two maps
compared *as maps*, and every route tried so far runs into the `L`-versus-`L(v)` scalar boundary:
`TensorProduct.ext'` wants both sides `L(v)`-linear, which needs
`LinearMap.CompatibleSMul (L ⊗[L(v)] W_v) (M(v)) (L(v)) L` — absent; pointwise induction needs the
transport non-opaque (fixed, it is a `def` now) *and* the `zero`/`add` cases, which `simp only
[map_zero]` / `rw [map_add]` do not close through the composite's coercions. This is the S5-F3
**boundary tax** in its purest form: the mathematics is `rfl` on generators and the cost is entirely
in getting the two scalar heads to meet.

The next attempt should build the comparison at the `AddMonoidHom` level, where no `CompatibleSMul`
is needed, using `TensorProduct.liftAddHom`'s uniqueness rather than `LinearMap` extensionality.

@census none (helper for `RQ2-2.21-C4`) -/
theorem vertexDescentMap_bijective (M : Rep Γ) (v : Γ.V) :
    Function.Bijective (vertexDescentMap M v) := by
  have h := Descent.descentCounit_bijective ↥(stabField K L v) L (Rep.vertexVecK M v)
  have hfun : (vertexDescentMap M v : _ → M.M v)
      = (Descent.descentCounit ↥(stabField K L v) L (Rep.vertexVecK M v))
        ∘ (vertexFixedTransport M v) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero =>
        show vertexDescentMap M v 0 = _
        rw [map_zero]
        show 0 = Descent.descentCounit _ L _ (vertexFixedTransport M v 0)
        rw [map_zero, map_zero]
    | tmul a m => rfl
    | add x y hx hy =>
        show vertexDescentMap M v (x + y) = _
        show _ = Descent.descentCounit _ L _ (vertexFixedTransport M v (x + y))
        rw [map_add, map_add, map_add]
        show vertexDescentMap M v x + vertexDescentMap M v y = _
        rw [hx, hy]
        rfl
  rw [hfun]
  exact h.comp (vertexFixedTransport M v).bijective

/-- `W_v`'s respelled-base action is the untwisted one — `rebase`'s compatibility argument.
@census none (helper) -/
theorem Rep.moduleTwistBase_vertexFixed_smul (M : Rep Γ) (v : Γ.V) (σ : Gal(L/K))
    (b : Twist.TwistBase (stabField K L v) σ) (w : ↥(M.vertexFixed v)) :
    b • w = (b.val : ↥(stabField K L v)) • w := rfl

/-- The descent, as an `L`-linear equivalence: `L ⊗_{L(v)} W_v ≅ M(v)`.
@census none (helper for `RQ2-2.21-C4`) -/
noncomputable def vertexDescentEquiv (M : Rep Γ) (v : Γ.V) :
    (L ⊗[↥(stabField K L v)] ↥(M.vertexFixed v)) ≃ₗ[L] M.M v :=
  LinearEquiv.ofBijective _ (vertexDescentMap_bijective M v)

@[simp]
theorem vertexDescentEquiv_tmul (M : Rep Γ) (v : Γ.V) (a : L) (m : ↥(M.vertexFixed v)) :
    vertexDescentEquiv M v (a ⊗ₜ m) = a • (m : M.M v) := rfl

/-! ### `W_v` is finite over `L(v)`  (G4, for `RQ2-2.26`'s `finite_W`)

`Species.Rep`'s `finite_W` field is `Module.Finite (L_i)ᵐᵒᵖ W_i`, and what `FDRep` gives is
`FiniteDimensional L (M(v))`.  Galois descent carries one to the other in two steps: the rank of
`L ⊗_{L(v)} W_v` over `L` **is** the rank of `W_v` over `L(v)` (`Module.rank_baseChange`), and
`vertexDescentEquiv` identifies that tensor with `M(v)`; then the opposite action, being the same
action read through `RingEquiv.toOpposite`, has the same spans.

@census none (helper for `RQ2-2.26`)
-/

/-- `W_v` is finite over `L(v)` when `M(v)` is finite over `L`: Galois descent transports
finite-dimensionality down. -/
theorem Rep.finite_vertexFixed (M : Rep Γ) (v : Γ.V) [FiniteDimensional L (M.M v)] :
    Module.Finite ↥(stabField K L v) ↥(M.vertexFixed v) := by
  have h1 : Module.rank L (L ⊗[↥(stabField K L v)] ↥(M.vertexFixed v)) < Cardinal.aleph0 := by
    rw [(vertexDescentEquiv M v).rank_eq]
    exact Module.rank_lt_aleph0 L (M.M v)
  rw [Module.rank_baseChange] at h1
  rw [← Module.rank_lt_aleph0_iff]
  simpa using h1

/-- …and over the opposite, which is the side `RQ2-2.17` puts `W_i` on. -/
theorem Rep.finite_op_vertexFixed (M : Rep Γ) (v : Γ.V) [FiniteDimensional L (M.M v)] :
    Module.Finite (↥(stabField K L v))ᵐᵒᵖ ↥(M.vertexFixed v) := by
  obtain ⟨S, hS⟩ := Module.finite_def.mp (M.finite_vertexFixed v)
  have key : ∀ x : ↥(M.vertexFixed v),
      x ∈ Submodule.span (↥(stabField K L v)) (S : Set ↥(M.vertexFixed v)) →
      x ∈ Submodule.span (↥(stabField K L v))ᵐᵒᵖ (S : Set ↥(M.vertexFixed v)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul c a _ ha =>
        have hc : (c • a : ↥(M.vertexFixed v)) = (MulOpposite.op c) • a := rfl
        rw [hc]
        exact Submodule.smul_mem _ _ ha
  exact Module.finite_def.mpr ⟨S, eq_top_iff.mpr fun x _ => key x (by rw [hS]; trivial)⟩

/-- **`RQ2-2.21`'s isomorphism, as the composite.**

  `Twist ⊗ W_v --untwist--> L ⊗ W_v --rebase--> L ⊗_{L(v)} W_v --descent--> M(v) --φ'_{v,σ}--> M(σv)`

Every leg is an equivalence, so the composite is one; `generalExtensionMap_eq_equiv` identifies it
with the source's `a ⊗ m ↦ a · φ'_{v,σ}(m)`.

@census none (helper for `RQ2-2.21-C4`) -/
noncomputable def generalExtensionEquiv (M : Rep Γ) (v : Γ.V) (σ : Gal(L/K)) :
    (Twist (stabField K L v) σ
        ⊗[Twist.TwistBase (stabField K L v) σ] ↥(M.vertexFixed v)) ≃+ M.M (σ • v) :=
  ((TensorProduct.congr (Twist.untwist (E := stabField K L v) (σ := σ))
      (LinearEquiv.refl (Twist.TwistBase (stabField K L v) σ)
        ↥(M.vertexFixed v))).toAddEquiv).trans
    ((Twist.rebase ↥(M.vertexFixed v) (M.moduleTwistBase_vertexFixed_smul v σ)).trans
      (((vertexDescentEquiv M v).toAddEquiv).trans (M.φ' σ rfl)))

/-- The composite **is** the source's map: on `ofL a ⊗ m` it telescopes to
`σ(σ⁻¹ a) · φ'_{v,σ}(m) = a · φ'_{v,σ}(m)`.  @census none (helper) -/
theorem generalExtensionMap_eq_equiv (M : Rep Γ) (v : Γ.V) (σ : Gal(L/K)) :
    ∀ x, generalExtensionMap M v σ x = generalExtensionEquiv M v σ x := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x m =>
      obtain ⟨a⟩ := x
      show a • M.φ' σ rfl (m : M.M v)
        = M.φ' σ rfl (vertexDescentEquiv M v (σ.symm a ⊗ₜ m))
      rw [vertexDescentEquiv_tmul, M.φ'_smul, AlgEquiv.apply_symm_apply]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- **Clause `RQ2-2.21-C4`**: the extension map is an isomorphism.

Galois descent (`RQ2-1.13`) is consumed here as a **proved theorem** — design decision `D1`'s
payoff, and the row the stage plan named as that decision's dividend.

@census none (clause witness for `RQ2-2.21-C4`)
@clauses   RQ2-2.21-C4 -/
theorem generalExtensionMap_bijective (M : Rep Γ) (v : Γ.V) (σ : Gal(L/K)) :
    Function.Bijective (generalExtensionMap M v σ) := by
  have h : (generalExtensionMap M v σ : _ → M.M (σ • v)) = generalExtensionEquiv M v σ :=
    funext (generalExtensionMap_eq_equiv M v σ)
  rw [h]
  exact (generalExtensionEquiv M v σ).bijective

/-- The extension map is `L`-linear.  The `L`-action on the source is on the `Twist` factor, so
this is `(c·a) · φ'_σ(m) = c · (a · φ'_σ(m))`.  @census none (helper) -/
theorem generalExtensionMap_smul (M : Rep Γ) (v : Γ.V) (σ : Gal(L/K)) (c : L)
    (x : Twist (stabField K L v) σ
        ⊗[Twist.TwistBase (stabField K L v) σ] ↥(M.vertexFixed v)) :
    generalExtensionMap M v σ (c • x) = c • generalExtensionMap M v σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul y m =>
      obtain ⟨a⟩ := y
      show (c * a) • M.φ' σ rfl (m : M.M v) = c • a • M.φ' σ rfl (m : M.M v)
      rw [mul_smul]
  | add p q hp hq => rw [smul_add, map_add, map_add, hp, hq, smul_add]

/-- `RQ2-2.21`'s extension, as an `L`-linear equivalence.  @census none (helper) -/
noncomputable def generalExtensionLinearEquiv (M : Rep Γ) (v : Γ.V) (σ : Gal(L/K)) :
    (Twist (stabField K L v) σ
        ⊗[Twist.TwistBase (stabField K L v) σ] ↥(M.vertexFixed v)) ≃ₗ[L] M.M (σ • v) :=
  { generalExtensionMap M v σ with
    map_smul' := generalExtensionMap_smul M v σ
    invFun := (Equiv.ofBijective _ (generalExtensionMap_bijective M v σ)).symm
    left_inv := (Equiv.ofBijective _ (generalExtensionMap_bijective M v σ)).symm_apply_apply
    right_inv := (Equiv.ofBijective _ (generalExtensionMap_bijective M v σ)).apply_symm_apply }

@[simp]
theorem generalExtensionLinearEquiv_tmul (M : Rep Γ) (v : Γ.V) (σ : Gal(L/K)) (a : L)
    (m : ↥(M.vertexFixed v)) :
    generalExtensionLinearEquiv M v σ (Twist.ofL a ⊗ₜ m) = a • M.φ σ v (m : M.M v) := rfl

/-- **Proposition `prop:generalextensionofscalars`** (census `RQ2-2.21`).

For any `v ∈ V` and any `σ ∈ G` (clause `RQ2-2.21-H1`) the given semi-linear map
`φ_{v,σ} : M(v) → M(σ v)` of a `K`-rational representation `M_K` (clause `RQ2-2.21-H2`) restricts to
`M(v)^{G_v} → M(σ v)` (clause `RQ2-2.21-C1`, the `M.φ σ v` on the right of the first conjunct) and
**extends** to an `L`-linear map

`M(v)^{G_v} ⊗_{L(v),σ} L → M(σ v)`,  `m ⊗ a ↦ φ_{v,σ}(m) · a`
  (`eq:generalextensionisomorphism`, clause `RQ2-2.21-C2`),

which is **unique** with that property (clause `RQ2-2.21-C3`, the second conjunct) and is an
**isomorphism** of `L`-vector spaces (clause `RQ2-2.21-C4`, the `≃ₗ[L]`).  Moreover for any `τ ∈ G`
the square `eq:semi-linearsquare` commutes, with top map `m ⊗ a ↦ m ⊗ τ(a)` and bottom map
`φ_{σ v, τ}` (clause `RQ2-2.21-C5`, the third conjunct).

@census    RQ2-2.21
@source    prop:generalextensionofscalars
@clauses   RQ2-2.21-H1, RQ2-2.21-H2, RQ2-2.21-C1, RQ2-2.21-C2, RQ2-2.21-C3, RQ2-2.21-C4, RQ2-2.21-C5
@imports   none
@divergence JUSTIFIED_REFORMULATION on clause `RQ2-2.21-C2`, on the two presentational points this
module's header records and nothing else: the tensor is written with the field on the left
(mathlib's base-change order), and `⊗_{L(v),σ}` — the twist named *after* the ring — is
`Twist (L(v)) σ`, the wrapper of `Species/Rep/Twist.lean` whose `smul_def` keeps the twist visible
in the elaborated signature.  The pure-tensor formula is therefore written `a ⊗ m ↦ a · φ_{v,σ}(m)`;
it is the source's, with the factors in mathlib's order.

The whole statement is quantified over `σ` *inside* the existential, rather than being one
proposition per `σ`, because clause `C5` relates the extensions for `σ` and for `τσ` and so needs
both at once — the same reason the source states it as one proposition with a "moreover".

Proof plan (G4), the source's own: existence and uniqueness are the universal property of
`M(v)^{G_v} ⊗_{L(v),σ} L`; that the map is an isomorphism is Galois descent (`RQ2-1.13`, stage S0's
`galoisDescent`, consumed as a *proved theorem* — this is the row the stage plan's §4 names as the
payoff of design decision D1); and `C5` is again the universal property, both sides being `L`-linear
maps agreeing on pure tensors.
-/
theorem generalExtension_of_scalars (M : Rep Γ) (v : Γ.V) :
    ∃ e : ∀ σ : Gal(L/K),
        (Twist (stabField K L v) σ
          ⊗[Twist.TwistBase (stabField K L v) σ] ↥(M.vertexFixed v)) ≃ₗ[L] M.M (σ • v),
      (∀ (σ : Gal(L/K)) (a : L) (m : ↥(M.vertexFixed v)),
          e σ (Twist.ofL a ⊗ₜ m) = a • M.φ σ v (m : M.M v)) ∧
      (∀ (σ : Gal(L/K))
          (f : (Twist (stabField K L v) σ
                  ⊗[Twist.TwistBase (stabField K L v) σ] ↥(M.vertexFixed v))
                →ₗ[L] M.M (σ • v)),
          (∀ (a : L) (m : ↥(M.vertexFixed v)),
              f (Twist.ofL a ⊗ₜ m) = a • M.φ σ v (m : M.M v)) → f = (e σ).toLinearMap) ∧
      (∀ (σ τ : Gal(L/K)) (a : L) (m : ↥(M.vertexFixed v)),
          M.φ' τ (mul_smul τ σ v).symm (e σ (Twist.ofL a ⊗ₜ m))
            = e (τ * σ) (Twist.ofL (τ a) ⊗ₜ m)) := by
  refine ⟨generalExtensionLinearEquiv M v, fun σ a m => rfl, ?_, ?_⟩
  · -- `C3`: uniqueness — two `L`-linear maps agreeing on pure tensors agree.
    intro σ f hf
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul y m =>
        obtain ⟨a⟩ := y
        rw [hf a m]
        rfl
    | add p q hp hq => rw [map_add, map_add, hp, hq]
  · -- `C5`: `eq:semi-linearsquare`, both sides `σ`-semi-linear and computed on pure tensors.
    intro σ τ a m
    show M.φ' τ (mul_smul τ σ v).symm (a • M.φ' σ rfl (m : M.M v))
      = τ a • M.φ' (τ * σ) rfl (m : M.M v)
    rw [M.φ'_smul]
    congr 1
    exact M.φ'_comp τ σ rfl (mul_smul τ σ v).symm rfl (m : M.M v)

/-! ### § Downstream guards (finding **V-S5b-13**)

`Species/Rep/Twist.lean`'s end-of-module guards prove the twisted action wins **inside that
module**.  They do not cover the *importer* case: a module downstream of `Twist.lean`'s whole
instance surface can see instances the guards never faced.  `CONVENTIONS.md` §3 therefore requires
the winning-`#synth` guard to exist as a permanent example downstream as well.  Here it is, in the
module where the respelled base is actually consumed.

@census none (instance guards, `DEF-S5-04`)
-/

section DownstreamGuards

/-- **V-S5b-13 guard.**  Downstream of `Twist.lean`'s entire instance surface, the synthesized
`SMul (TwistBase E σ) (Twist E σ)` is still the **twisted** one.  Bare `•`, proved by `rfl`, so it
breaks the build if any instance visible here shadows `Twist.algebraBase`.

@census none (instance guard) -/
theorem twistBase_smul_guard_downstream (E : IntermediateField K L) (σ : Gal(L/K))
    (b : Twist.TwistBase E σ) (x : Twist E σ) :
    b • x = Twist.ofL (σ ((b.val : ↥E) : L) * x.val) := rfl

end DownstreamGuards

/-! ### `RQ2-2.20` — `eq:WiiMjLpre`

Six more head bridges, all of the shape `DESIGN-NOTES` §12 describes and none of them new
mathematics: the outer base change `(W_i ⊗_{L_i} {}_iM_j) ⊗_{L_j} L` is `Balanced` with `A = L_j`,
`B = Y = L`, and every one of `Balanced`'s standing assumptions has to be produced at the
`Γ.toSpecies.L j` head rather than at `stabField K L (Γ.vertexRep j)`.  Each is literally the
instance it re-heads.
-/

/-- `L` as an `L_i`-vector space, at the species head.  @census none (helper) -/
noncomputable instance moduleSpeciesL (i : Γ.VertexOrbit) : Module (Γ.toSpecies.L i) L :=
  inferInstanceAs (Module ↥(stabField K L (Γ.vertexRep i)) L)

/-- @census none (helper) -/
instance towerSpeciesL (i : Γ.VertexOrbit) : IsScalarTower K (Γ.toSpecies.L i) L :=
  inferInstanceAs (IsScalarTower K ↥(stabField K L (Γ.vertexRep i)) L)

/-- @census none (helper) -/
instance towerSpeciesLL (i : Γ.VertexOrbit) : IsScalarTower (Γ.toSpecies.L i) L L :=
  inferInstanceAs (IsScalarTower ↥(stabField K L (Γ.vertexRep i)) L L)

/-- `L_i` and the right `L`-action on `L` commute — associativity in `L`.
@census none (helper) -/
instance smulCommSpeciesL (i : Γ.VertexOrbit) : SMulCommClass (Γ.toSpecies.L i) Lᵐᵒᵖ L where
  smul_comm a b x := by
    show a • (x * MulOpposite.unop b) = (a • x) * MulOpposite.unop b
    exact (smul_mul_assoc a x (MulOpposite.unop b)).symm

/-- `W_i` as an `L(v_i)`-space, at the `vertexOrbitField` head.  @census none (helper) -/
noncomputable instance moduleVOF_vertexFixed (M : Rep Γ) (i : Γ.VertexOrbit) :
    Module ↥(Γ.vertexOrbitField i) ↥(M.vertexFixed (Γ.vertexRep i)) :=
  inferInstanceAs (Module ↥(stabField K L (Γ.vertexRep i)) _)

/-- When the far side of a balanced product is `L` itself, the result is an `L`-vector space in the
ordinary (non-opposite) sense, `L` being commutative.  This is what lets `eq:WiiMjLpre` be an
isomorphism **of `L`-vector spaces**, as the source says, rather than of `Lᵐᵒᵖ`-modules.

@census none (helper)
-/
noncomputable instance moduleL_balancedOverL (A : Type u) [Ring A] [Algebra K A]
    (X : Type u) [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X] [IsScalarTower K Aᵐᵒᵖ X]
    [Module A L] [IsScalarTower K A L] [SMulCommClass A Lᵐᵒᵖ L] :
    Module L (Balanced K A L L X) :=
  inferInstanceAs (Module L ((L ⊗[K] X) ⧸ balancedRel K A L L X))

/-- **Coherence guard for `moduleL_balancedOverL`** (finding `S5-F7`, `DESIGN-NOTES` §52;
coordinator-sanctioned normalisation).

The `SMul`-query and the `Module`-query on `X ⊗_A L` must reach **the same** action.  They did
not while this instance was `Module.compHom _ (RingEquiv.toOpposite L).toRingHom`: the `Module`
was correct and unique, its `toSMul` was not `Submodule.Quotient.instSMul'`, and no lemma written
with `•` could then discharge a `≃ₗ[L]`'s `map_smul`.  Re-implemented by **forgetful
inheritance** — the module is the quotient's own — this is `rfl`, and it is the permanent
acceptance test for that.

If this breaks, the two queries have diverged again and every `≃ₗ[L]` over a `Balanced` is
unprovable from `•`-lemmas.  @census none (guard, `CONVENTIONS.md` §3) -/
example (A : Type u) [Ring A] [Algebra K A]
    (X : Type u) [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X] [IsScalarTower K Aᵐᵒᵖ X]
    [Module A L] [IsScalarTower K A L] [SMulCommClass A Lᵐᵒᵖ L] :
    (inferInstance : SMul L (Balanced K A L L X))
      = (inferInstance : Module L (Balanced K A L L X)).toSMul := rfl

section BalancedLGuards

variable (A : Type u) [Ring A] [Algebra K A]
  (X : Type u) [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X] [IsScalarTower K Aᵐᵒᵖ X]
  [Module A L] [IsScalarTower K A L] [SMulCommClass A Lᵐᵒᵖ L]

/-- **Guard 1 (value of the winning action).**  The `L`-action that synthesis picks on
`X ⊗_A L` multiplies in `L`, on the nose.  `rfl`.  @census none (guard) -/
theorem balanced_smul_L_mk (c a : L) (t : X) :
    (c • Balanced.mk (K := K) (A := A) (B := L) t a)
      = Balanced.mk (K := K) (A := A) (B := L) t (c * a) := rfl

/-- **Guard 2 (value of the `ᵐᵒᵖ` action).**  The `Lᵐᵒᵖ`-action lands on the same value — via
`Balanced.smul_mk` and one `mul_comm`, `L` being commutative.  @census none (guard) -/
theorem balanced_smul_op_mk (c a : L) (t : X) :
    (MulOpposite.op c • Balanced.mk (K := K) (A := A) (B := L) t a)
      = Balanced.mk (K := K) (A := A) (B := L) t (c * a) := by
  rw [Balanced.smul_mk]
  congr 1
  show a * c = c * a
  exact mul_comm a c

/-- **The bridge (finding `S5-F7`).**  The `L`- and `Lᵐᵒᵖ`-actions on `X ⊗_A L` agree.

They are **not** definitionally equal — see `S5-F7` in `DESIGN-NOTES` — so this is proved by
quotient induction, and on a generator by routing both sides through the common value the two
guards above compute.  Every proof that must move an `L`-scalar across `Balanced`'s `≃ₗ[L]`
statements goes through here.

@census none (helper, finding `S5-F7`) -/
theorem balanced_smul_L_eq_op (c : L) (z : Balanced K A L L X) :
    c • z = MulOpposite.op c • z := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K A L L X) z
  induction y with
  | zero => simp
  | tmul a t => exact (balanced_smul_L_mk A X c a t).trans (balanced_smul_op_mk A X c a t).symm
  | add p q hp hq =>
      have hmk : Submodule.Quotient.mk (p := balancedRel K A L L X) (p + q)
          = Submodule.Quotient.mk p + Submodule.Quotient.mk q := rfl
      rw [hmk, smul_add, smul_add, hp, hq]

end BalancedLGuards

/-! ### `RQ2-2.20` items 2+5: `eq:edgediagram`'s **left** half, and why it cannot be an instance

`{}_iM_j = ⊕_ε L(e_ε)` splits, and the moment it does, `L_i` starts acting on each `L(e_ε)`
through `edgeComponentLeft` — "apply `σ_ε`".  So the `σ_ε` twist is **load-bearing for the
distribution**, not only for the composition that follows it: it enters with the splitting.
That is `eq:edgediagram`'s left half (`RQ2-2.09-C4`) arriving exactly where the diagram says it
should, and it is why items 2 and 5 are one piece of work rather than two.

**The architectural constraint, measured.**  `edgeLeftAlgebra` and `edgeRightAlgebra` are the two
halves of `eq:edgediagram`, and at a **loop** orbit — `ε : Γ.EdgeOrbit i i`, a perfectly ordinary
quiver — they inhabit *literally the same type*,

  `Algebra ↥(Γ.vertexOrbitField i) ↥(Γ.edgeOrbitField ε)`,

with **different** structure maps (`σ_ε` versus `τ_ε`; `edgeComponentRight_coe_tau`).  Two
inhabitants of one class at one head is ambiguity, and which one instance search picks is
arbitrary — the `S5-F5` failure mode with the competitor supplied by the *mathematics* rather than
by an accident of `SetLike`.  `RQ2-2.20` needs **both** at once (the left for the splitting, the
right for `RQ2-2.19`'s hypothesis), so in its construction **neither may be ambient**: both are
plain `def`s, applied explicitly.

`edgeRightAlgebra`'s `attribute [local instance]` is confined to `section EdgeRight`, where only
the right half is in play; that remains correct and is why it was safe there.

@census none (G4 engine for `RQ2-2.20`)
-/

/-- **`eq:edgediagram`'s left half as an algebra structure**: `L(e_ε)` over `L_i`, along
`edgeComponentLeft` — i.e. "apply `σ_ε`".  The mirror of `edgeRightAlgebra`.

**Not an instance, and — unlike its mirror — not even a section-local one.**  See the section
header: at a loop orbit the two halves have the same type and different content, and `RQ2-2.20`
needs both simultaneously.  Applied explicitly wherever it is used.

@census none (helper for `RQ2-2.20`; `RQ2-2.09-C4` left half) -/
@[reducible] noncomputable def edgeLeftAlgebra {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) :
    Algebra ↥(Γ.vertexOrbitField i) ↥(Γ.edgeOrbitField ε) :=
  RingHom.toAlgebra (Γ.edgeComponentLeft ε).toRingHom

/-- The left structure map is "apply `σ_ε`", the mirror of `edgeComponentRight_coe_tau`.

Same three ingredients: `edgeComponentLeft_coe` states it via the `choose`,
`stabField_apply_eq_of_smul_eq` says the choice does not matter, and `ch.source_eq` certifies
`σ_ε` as a legitimate alternative.

@census none (helper for `RQ2-2.20`) -/
theorem edgeComponentLeft_coe_sigma {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (b : ↥(Γ.vertexOrbitField i)) :
    ((Γ.edgeComponentLeft ε b : ↥(Γ.edgeOrbitField ε)) : L) = ch.σ (b : L) := by
  rw [Γ.edgeComponentLeft_coe ε b]
  exact stabField_apply_eq_of_smul_eq
    (((mem_orbit_iff.mp (Γ.source_edgeRep_mem_orbit ε)).choose_spec).trans ch.source_eq.symm) b

/-! ### `RQ2-2.20` item 2: the inner balanced product, and the splitting of `{}_iM_j`

Three more head bridges of the `S5-F3` kind, then `Balanced.equivTensor` again.

`EtaleSpecies.moduleLeft` already gives `L_i` acting on `{}_iM_j` (through the species' `left`,
which is `Pi.algHom` of the `edgeComponentLeft`s), so the inner product needs **no** `σ_ε` at this
level — the twist appears only when the `∀ ε` is split, and `edgeLeftAlgebraSpecies_smul_apply`
below is the `rfl` that says the species' componentwise action **is** `edgeLeftAlgebra` factor by
factor.  That lemma is the hinge of the splitting step.

@census none (G4 engine for `RQ2-2.20`)
-/

/-- The **left** `L_i`-structure on `W_i`, at the species head.  `Rep.moduleL_W` is the same
construction for a species representation's `W i`; this is it for a `RationalQuiver` one, where
the carrier is `M.vertexFixed (Γ.vertexRep i)`.  @census none (helper, `S5-F3`) -/
noncomputable instance moduleSpeciesLi_vertexFixed (M : Rep Γ) (i : Γ.VertexOrbit) :
    Module (Γ.toSpecies.L i) ↥(M.vertexFixed (Γ.vertexRep i)) :=
  moduleOfOpposite _ _

/-- …and its ambient `K`-structure is the induced one.  @census none (helper, `S5-F3`) -/
instance towerK_speciesLi_vertexFixed (M : Rep Γ) (i : Γ.VertexOrbit) :
    IsScalarTower K (Γ.toSpecies.L i) ↥(M.vertexFixed (Γ.vertexRep i)) where
  smul_assoc c a x := by
    show (MulOpposite.op (c • a)) • x = c • ((MulOpposite.op a) • x)
    rw [← smul_assoc c (MulOpposite.op a) x]
    congr 1

/-- `edgeLeftAlgebra` at the species head.  Still **not an instance** — §51's constraint is about
the mathematics, not the spelling, and re-heading does not change it.
@census none (helper, `S5-F3`) -/
@[reducible] noncomputable def edgeLeftAlgebraSpecies {i j : Γ.VertexOrbit}
    (ε : Γ.EdgeOrbit i j) : Algebra (Γ.toSpecies.L i) ↥(Γ.edgeOrbitField ε) :=
  edgeLeftAlgebra ε

/-- **The hinge of the splitting step**: the species' action of `L_i` on `{}_iM_j = ∀ ε, L(e_ε)`
is `edgeLeftAlgebra` **factor by factor**, on the nose.

`Γ.toSpecies.left` is `Pi.algHom K _ (fun ε => Γ.edgeComponentLeft ε)`, so this is `rfl` — but it
is the fact that lets `TensorProduct.piLeft` split the inner product into its edge-orbit summands
with each summand carrying the `σ_ε`-twisted structure the source's `eq:edgediagram` prescribes.

@census none (helper for `RQ2-2.20-C2`) -/
theorem edgeLeftAlgebraSpecies_smul_apply {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (b : Γ.toSpecies.L i) (m : Γ.toSpecies.M i j) :
    (b • m) ε = (letI := edgeLeftAlgebraSpecies ε; b • m ε) := rfl

/-- **`RQ2-2.20` item 2, first half.**  `W_i ⊗_{L_i} {}_iM_j = {}_iM_j ⊗[L_i] W_i`, mathlib's
spelling on the right.  `hX` is `rfl`, as in `outerEquiv`.
@census none (helper for `RQ2-2.20-C1`) -/
noncomputable def innerEquiv (M : Rep Γ) (i j : Γ.VertexOrbit) :
    EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
      ≃ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ]
      (Γ.toSpecies.M i j ⊗[Γ.toSpecies.L i] ↥(M.vertexFixed (Γ.vertexRep i))) :=
  Balanced.equivTensor (B := Γ.toSpecies.L j) (fun _ _ => rfl)

/-- `innerEquiv` on a pure tensor, by `rfl`.  @census none (helper) -/
@[simp] theorem innerEquiv_mk (M : Rep Γ) (i j : Γ.VertexOrbit)
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) :
    innerEquiv M i j (Balanced.mk w m) = m ⊗ₜ[Γ.toSpecies.L i] w := rfl

/-! ### The twist absorbs its own base  (G4, for `RQ2-2.27-C5`)

`RQ2-2.20`'s chain cancels `L(e_ε)` and composes the two twists into one (`edgeCancel`).
`RQ2-2.27-C5` takes the other route the source offers — apply clause `C4` **first**, replacing
`W_i` by `W_{i,K} ⊗_K L_i`, after which the summand is `L(e_ε) ⊗_K W_{i,K}` and the remaining step
has **no output twist at all**:

  `Twist(E,ρ) ⊗_{TwistBase(E,ρ)} (E ⊗_K W)  ≅  L ⊗_K W`,   `t ⊗ (x ⊗ w) ↦ (t · ρx) ⊗ w`.

**Built directly on generators, and the reason is measured rather than inherited.**  The obvious
composite factors through `Twist.untwist`; it cannot, because `untwist_smulL` shows `untwist` is
**`ρ⁻¹`-semi-linear** for the two `L`-structures, so nothing through it is `L`-linear.  That is the
same obstruction `edgeCancel` met (§'s item 5), met again here for the same reason.

The content is in the two balance conditions: over `TwistBase` the `ρ` has to absorb the base
element on both sides, and over `K` the scalar has to cross `ρ` — which `ρ.commutes` permits, and
which is the only place `E`'s being an *intermediate* field is used.

**`left_inv` and the `smul` law are term-mode on purpose** (`congrArg`/`trans` rather than `rw`).
`CONVENTIONS.md` §3's timeout entry, in the `§55.4` presentation: on these carriers a `rw`'s
**motive check** exhausts 200 000 heartbeats where the term it stands for elaborates instantly.
Diagnosed, not dialled around.

@census none (G4 engine for `RQ2-2.27-C5`)
-/

section TwistAbsorb

variable (E : IntermediateField K L) (ρ : Gal(L/K))
  (W : Type u) [AddCommGroup W] [Module K W]

/-- `E ⊗_K W` as a `TwistBase E ρ`-module, through `toE` — the untwisted reading. -/
noncomputable instance moduleTwistBase_tensorK :
    Module (Twist.TwistBase E ρ) (↥E ⊗[K] W) :=
  Module.compHom _ Twist.TwistBase.toE

theorem twistBase_smul_tensorK (b : Twist.TwistBase E ρ) (z : ↥E ⊗[K] W) :
    b • z = (b.val : ↥E) • z := rfl

/-- The inner map of `twistAbsorb`: for a fixed `t`, `x ⊗ w ↦ (t · ρ x) ⊗ w`. -/
noncomputable def twistAbsorbInner (t : Twist E ρ) : (↥E ⊗[K] W) →+ (L ⊗[K] W) :=
  TensorProduct.liftAddHom
    { toFun := fun x =>
        { toFun := fun w => (t.val * ρ ((x : L))) ⊗ₜ[K] w
          map_zero' := TensorProduct.tmul_zero _ _
          map_add' := fun _ _ => TensorProduct.tmul_add _ _ _ }
      map_zero' := by
        ext w
        show (t.val * ρ (((0 : ↥E)) : L)) ⊗ₜ[K] w = 0
        rw [show (((0 : ↥E)) : L) = 0 from rfl, map_zero, mul_zero]
        exact TensorProduct.zero_tmul _ _
      map_add' := fun x y => by
        ext w
        show (t.val * ρ (((x + y : ↥E)) : L)) ⊗ₜ[K] w = _ + _
        rw [show (((x + y : ↥E)) : L) = (x : L) + (y : L) from rfl, map_add, mul_add]
        exact TensorProduct.add_tmul _ _ _ }
    (fun c x w => by
      show (t.val * ρ (((c • x : ↥E)) : L)) ⊗ₜ[K] w
        = (t.val * ρ ((x : ↥E) : L)) ⊗ₜ[K] (c • w)
      rw [show (((c • x : ↥E)) : L) = (algebraMap K L c) * (x : L) from by
          rw [Algebra.smul_def]; rfl, map_mul,
        show ρ (algebraMap K L c) = algebraMap K L c from ρ.commutes c, ← mul_assoc,
        mul_comm t.val (algebraMap K L c), mul_assoc]
      rw [show ((algebraMap K L c) * (t.val * ρ ((x : ↥E) : L)))
          = c • (t.val * ρ ((x : ↥E) : L)) from (Algebra.smul_def c _).symm,
        TensorProduct.smul_tmul])

@[simp] theorem twistAbsorbInner_tmul (t : Twist E ρ) (x : ↥E) (w : W) :
    twistAbsorbInner E ρ W t (x ⊗ₜ[K] w) = (t.val * ρ ((x : L))) ⊗ₜ[K] w := rfl

theorem twistAbsorbInner_zero : twistAbsorbInner E ρ W 0 = 0 := by
  refine AddMonoidHom.ext fun z => ?_
  simp only [AddMonoidHom.zero_apply]
  induction z using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul x w =>
      rw [twistAbsorbInner_tmul, show ((0 : Twist E ρ).val) = 0 from rfl, zero_mul]
      exact TensorProduct.zero_tmul _ _
  | add p q hp hq => rw [map_add, hp, hq, add_zero]

theorem twistAbsorbInner_add (t t' : Twist E ρ) :
    twistAbsorbInner E ρ W (t + t')
      = twistAbsorbInner E ρ W t + twistAbsorbInner E ρ W t' := by
  refine AddMonoidHom.ext fun z => ?_
  simp only [AddMonoidHom.add_apply]
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | tmul x w =>
      rw [twistAbsorbInner_tmul, twistAbsorbInner_tmul, twistAbsorbInner_tmul,
        Twist.val_add, add_mul]
      exact TensorProduct.add_tmul _ _ _
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]; abel

theorem twistAbsorbInner_smul (c : L) (t : Twist E ρ) (y : ↥E ⊗[K] W) :
    twistAbsorbInner E ρ W (c • t) y = c • twistAbsorbInner E ρ W t y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul x w =>
      rw [twistAbsorbInner_tmul, twistAbsorbInner_tmul, Twist.val_smulL,
        TensorProduct.smul_tmul', mul_assoc, smul_eq_mul]
  | add p q hp hq => rw [map_add, map_add, hp, hq, smul_add]

/-- **The twist absorbs its own base**, forward map:
`Twist(E,ρ) ⊗_{TwistBase} (E ⊗_K W) → L ⊗_K W`, `t ⊗ (x ⊗ w) ↦ (t · ρx) ⊗ w`.

Built **directly on generators**.  The composite through `Twist.untwist` is not available:
`untwist_smulL` shows `untwist` is `ρ⁻¹`-semi-linear for the two `L`-structures, so nothing
factoring through it is `L`-linear.  Same measured obstruction as `edgeCancel`'s. -/
noncomputable def twistAbsorbFwd :
    (Twist E ρ ⊗[Twist.TwistBase E ρ] (↥E ⊗[K] W)) →+ (L ⊗[K] W) :=
  TensorProduct.liftAddHom
    { toFun := fun t => twistAbsorbInner E ρ W t
      map_zero' := twistAbsorbInner_zero E ρ W
      map_add' := twistAbsorbInner_add E ρ W }
    (fun b t z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x w =>
          show twistAbsorbInner E ρ W (b • t) (x ⊗ₜ[K] w)
            = twistAbsorbInner E ρ W t (b • (x ⊗ₜ[K] w))
          rw [twistAbsorbInner_tmul,
            show (b • (x ⊗ₜ[K] w) : ↥E ⊗[K] W) = ((b.val : ↥E) * x) ⊗ₜ[K] w from by
              rw [twistBase_smul_tensorK, TensorProduct.smul_tmul']; rfl,
            twistAbsorbInner_tmul, Twist.val_smulL_base,
            show ((((b.val : ↥E) * x : ↥E)) : L) = ((b.val : ↥E) : L) * (x : L) from rfl,
            map_mul]
          ring_nf
      | add p q hp hq => rw [smul_add, map_add, map_add, hp, hq])

@[simp] theorem twistAbsorbFwd_tmul (t : Twist E ρ) (x : ↥E) (w : W) :
    twistAbsorbFwd E ρ W (t ⊗ₜ[Twist.TwistBase E ρ] (x ⊗ₜ[K] w))
      = (t.val * ρ ((x : L))) ⊗ₜ[K] w := rfl

/-- The inverse: `a ⊗ w ↦ ofL a ⊗ (1 ⊗ w)`. -/
noncomputable def twistAbsorbBwd :
    (L ⊗[K] W) →+ (Twist E ρ ⊗[Twist.TwistBase E ρ] (↥E ⊗[K] W)) :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun w =>
            (Twist.ofL a : Twist E ρ)
              ⊗ₜ[Twist.TwistBase E ρ] ((1 : ↥E) ⊗ₜ[K] w)
          map_zero' := by
            rw [TensorProduct.tmul_zero]
            exact TensorProduct.tmul_zero _ _
          map_add' := fun w w' => by
            rw [TensorProduct.tmul_add]
            exact TensorProduct.tmul_add _ _ _ }
      map_zero' := by
        ext w
        show (Twist.ofL (0 : L) : Twist E ρ) ⊗ₜ[Twist.TwistBase E ρ] _ = 0
        rw [show (Twist.ofL (0 : L) : Twist E ρ) = 0 from rfl]
        exact TensorProduct.zero_tmul _ _
      map_add' := fun a a' => by
        ext w
        show (Twist.ofL (a + a') : Twist E ρ) ⊗ₜ[Twist.TwistBase E ρ] _ = _ + _
        rw [show (Twist.ofL (a + a') : Twist E ρ) = Twist.ofL a + Twist.ofL a' from rfl]
        exact TensorProduct.add_tmul _ _ _ }
    (fun c a w => by
      show (Twist.ofL (c • a) : Twist E ρ) ⊗ₜ[Twist.TwistBase E ρ] ((1 : ↥E) ⊗ₜ[K] w)
        = (Twist.ofL a : Twist E ρ) ⊗ₜ[Twist.TwistBase E ρ] ((1 : ↥E) ⊗ₜ[K] (c • w))
      have hb : (Twist.ofL (c • a) : Twist E ρ)
          = (Twist.TwistBase.ofE (algebraMap K ↥E c) : Twist.TwistBase E ρ)
              • (Twist.ofL a : Twist E ρ) := by
        apply Twist.val_injective
        rw [Twist.val_smulL_base]
        show c • a = ρ (((algebraMap K ↥E c : ↥E)) : L) * a
        rw [show (((algebraMap K ↥E c : ↥E)) : L) = algebraMap K L c from rfl,
          ρ.commutes c, Algebra.smul_def]
      rw [hb, TensorProduct.smul_tmul]
      congr 1
      rw [twistBase_smul_tensorK, TensorProduct.smul_tmul', ← TensorProduct.smul_tmul]
      congr 1
      show ((algebraMap K ↥E c : ↥E)) • (1 : ↥E) = c • (1 : ↥E)
      rw [Algebra.smul_def, Algebra.smul_def, Algebra.algebraMap_self_apply])

@[simp] theorem twistAbsorbBwd_tmul (a : L) (w : W) :
    twistAbsorbBwd E ρ W (a ⊗ₜ[K] w)
      = (Twist.ofL a : Twist E ρ) ⊗ₜ[Twist.TwistBase E ρ] ((1 : ↥E) ⊗ₜ[K] w) := rfl

/-- **The twist absorbs its own base**: `Twist(E,ρ) ⊗_{TwistBase(E,ρ)} (E ⊗_K W) ≅ L ⊗_K W`,
`L`-linearly. -/
noncomputable def twistAbsorb :
    (Twist E ρ ⊗[Twist.TwistBase E ρ] (↥E ⊗[K] W)) ≃ₗ[L] (L ⊗[K] W) :=
  AddEquiv.toLinearEquiv
    { toFun := twistAbsorbFwd E ρ W
      invFun := twistAbsorbBwd E ρ W
      map_add' := map_add _
      left_inv := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul t y =>
            induction y using TensorProduct.induction_on with
            | zero => simp
            | tmul x w =>
                have h1 : (Twist.ofL (t.val * ρ ((x : L))) : Twist E ρ)
                    = ((Twist.TwistBase.ofE x : Twist.TwistBase E ρ) • t) := by
                  apply Twist.val_injective
                  rw [Twist.val_smulL_base]
                  show t.val * ρ ((x : L)) = ρ ((x : L)) * t.val
                  exact mul_comm _ _
                have h2 : ((Twist.TwistBase.ofE x : Twist.TwistBase E ρ)
                      • ((1 : ↥E) ⊗ₜ[K] w) : ↥E ⊗[K] W)
                    = (x ⊗ₜ[K] w : ↥E ⊗[K] W) := by
                  rw [twistBase_smul_tensorK, TensorProduct.smul_tmul']
                  congr 1
                  show (x : ↥E) • (1 : ↥E) = x
                  rw [smul_eq_mul, mul_one]
                exact ((congrArg
                      (fun u : Twist E ρ =>
                        u ⊗ₜ[Twist.TwistBase E ρ] ((1 : ↥E) ⊗ₜ[K] w)) h1).trans
                    (TensorProduct.smul_tmul _ _ _)).trans
                  (congrArg (fun u : ↥E ⊗[K] W => t ⊗ₜ[Twist.TwistBase E ρ] u) h2)
            | add p q hp hq =>
                exact (congrArg (twistAbsorbBwd E ρ W ∘ twistAbsorbFwd E ρ W)
                    (TensorProduct.tmul_add t p q)).trans
                  (((map_add _ _ _).trans
                      (congrArg₂ (· + ·)
                        (congrArg (twistAbsorbBwd E ρ W) rfl) rfl)).trans
                    ((congrArg₂ (· + ·) hp hq).trans
                      (TensorProduct.tmul_add t p q).symm))
        | add p q hp hq =>
            exact ((congrArg (twistAbsorbBwd E ρ W) (map_add _ p q)).trans
              ((map_add _ _ _).trans (congrArg₂ (· + ·) hp hq)))
      right_inv := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a w =>
            show twistAbsorbFwd E ρ W (twistAbsorbBwd E ρ W (a ⊗ₜ[K] w)) = _
            rw [twistAbsorbBwd_tmul, twistAbsorbFwd_tmul]
            congr 1
            show (Twist.ofL a : Twist E ρ).val * ρ (((1 : ↥E)) : L) = a
            rw [show (((1 : ↥E)) : L) = 1 from rfl, map_one, mul_one]
        | add p q hp hq => rw [map_add, map_add, hp, hq] }
    (fun c z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul t y =>
          show twistAbsorbFwd E ρ W ((c • t) ⊗ₜ[Twist.TwistBase E ρ] y)
            = c • twistAbsorbFwd E ρ W (t ⊗ₜ[Twist.TwistBase E ρ] y)
          exact twistAbsorbInner_smul E ρ W c t y
      | add p q hp hq =>
          exact ((congrArg (twistAbsorbFwd E ρ W) (smul_add c p q)).trans
            ((map_add _ _ _).trans ((congrArg₂ (· + ·) hp hq).trans
              ((smul_add c (twistAbsorbFwd E ρ W p) (twistAbsorbFwd E ρ W q)).symm.trans
                (congrArg (fun u => c • u) (map_add (twistAbsorbFwd E ρ W) p q).symm))))))

@[simp] theorem twistAbsorb_tmul (t : Twist E ρ) (x : ↥E) (w : W) :
    twistAbsorb E ρ W (t ⊗ₜ[Twist.TwistBase E ρ] (x ⊗ₜ[K] w))
      = (t.val * ρ ((x : L))) ⊗ₜ[K] w := rfl

end TwistAbsorb

/-! ### The per-edge-orbit summand, at an **arbitrary** carrier  (G4)

`RQ2-2.20` needs this at `X = M(v_i)^{G_{v_i}}`; `RQ2-2.27-C5` needs the very same construction at an
arbitrary right `L_i`-space `V.W i`.  Nothing in the chain depends on which — so the carrier is a
parameter here, and the `RQ2-2.20`-side names below are **instantiations, not copies**.

That distinction is the point.  Two definitions of one object is the `S5-F5`/§51 failure mode, and
it would show up here as two `Module ↥(L(e_ε))` instances at one head; there is exactly one of each
instance below, keyed to the generic carrier, and the specialised names reduce to it.

@census none (G4 engine for `RQ2-2.20` and `RQ2-2.27-C5`)
-/

section GenericSummand

variable {i j : Γ.VertexOrbit} (X : Type u) [AddCommGroup X] [Module K X]
  [Module (Γ.toSpecies.L i) X]

/-- **The per-edge-orbit summand** `L(e_ε) ⊗_{L_i,σ_ε} X`.

`edgeLeftAlgebra` is supplied **explicitly** by a `letI` in the body, never resolved: §51 forbids
it being an instance, because at a loop orbit it and `edgeRightAlgebra` inhabit the same type with
different content.  An `abbrev`, so the `letI` unfolds and the elaborated type is the honest tensor
product.  @census none (helper for `RQ2-2.20-C2`, `RQ2-2.27-C5`) -/
noncomputable abbrev edgeSummandG (ε : Γ.EdgeOrbit i j) : Type u :=
  letI := edgeLeftAlgebraSpecies ε
  ↥(Γ.edgeOrbitField ε) ⊗[Γ.toSpecies.L i] X

/-- `L(e_ε)` acts on the summand, on its left factor.  Carrier-keyed (§51).
@census none (helper) -/
noncomputable instance moduleEdgeField_edgeSummandG (ε : Γ.EdgeOrbit i j) :
    Module ↥(Γ.edgeOrbitField ε) (edgeSummandG X ε) := by
  letI := edgeLeftAlgebraSpecies ε
  infer_instance

/-- …and so does the respelled base, through `toE` — the untwisted reading, which is what
`RQ2-2.19`'s `hVT` asks for.  @census none (helper) -/
noncomputable instance moduleTwistBase_edgeSummandG (ε : Γ.EdgeOrbit i j) (ρ : Gal(L/K)) :
    Module (Twist.TwistBase (Γ.edgeOrbitField ε) ρ) (edgeSummandG X ε) :=
  Module.compHom _ Twist.TwistBase.toE

/-- **`RQ2-2.19`'s `hVT`, discharged for the summand** — by `rfl`.  @census none (helper) -/
theorem twistBase_smul_edgeSummandG (ε : Γ.EdgeOrbit i j) (ρ : Gal(L/K))
    (b : Twist.TwistBase (Γ.edgeOrbitField ε) ρ) (s : edgeSummandG X ε) :
    b • s = (b.val : ↥(Γ.edgeOrbitField ε)) • s := rfl

/-- `L_j` acts on the summand through `edgeComponentRight` on its left factor —
`eq:edgediagram`'s **right** half.  Carrier-keyed (§51).  @census none (helper) -/
noncomputable instance moduleVOFj_edgeSummandG (ε : Γ.EdgeOrbit i j) :
    Module ↥(Γ.vertexOrbitField j) (edgeSummandG X ε) :=
  Module.compHom _ (Γ.edgeComponentRight ε).toRingHom

/-- **`RQ2-2.19`'s `hV`, discharged for the summand** — by `rfl`.  @census none (helper) -/
theorem hV_edgeSummandG (ε : Γ.EdgeOrbit i j) (a : ↥(Γ.vertexOrbitField j))
    (v : edgeSummandG X ε) : a • v = (Γ.edgeComponentRight ε a) • v := rfl

/-- A pure tensor of the summand.  @census none (helper) -/
noncomputable def edgeSummandMkG (ε : Γ.EdgeOrbit i j)
    (x : ↥(Γ.edgeOrbitField ε)) (w : X) : edgeSummandG X ε :=
  letI := edgeLeftAlgebraSpecies ε
  x ⊗ₜ[Γ.toSpecies.L i] w

/-- `L(e_ε)` acts through the left factor, on the nose.  @census none (helper) -/
theorem edgeField_smul_edgeSummandMkG (ε : Γ.EdgeOrbit i j)
    (y x : ↥(Γ.edgeOrbitField ε)) (w : X) :
    y • edgeSummandMkG X ε x w = edgeSummandMkG X ε (y * x) w := rfl

/-- **`RQ2-2.19` consumed, at an arbitrary carrier.**  Both hypotheses discharge by `rfl`.
@census none (helper for `RQ2-2.20-C1`, `RQ2-2.27-C5`) -/
theorem leEpsilon_at_edgeSummandG {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε) :
    ∃ e : (L ⊗[↥(Γ.vertexOrbitField j)] edgeSummandG X ε) ≃ₗ[L]
        (∀ η : EdgeChoice.CosetIndex Γ ch,
          Twist (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)
            ⊗[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)]
              edgeSummandG X ε),
      ∀ (a : L) (v : edgeSummandG X ε) (η : EdgeChoice.CosetIndex Γ ch),
        e (a ⊗ₜ[↥(Γ.vertexOrbitField j)] v) η
          = Twist.ofL a
              ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)] v :=
  Γ.leEpsilon_decomposition ch (edgeSummandG X ε) (hV_edgeSummandG X ε)
    (fun τ => twistBase_smul_edgeSummandG X ε τ)

end GenericSummand

/-- **The per-edge-orbit summand** `L(e_ε) ⊗_{L_i, σ_ε} W_i`.

`edgeLeftAlgebra` is supplied **explicitly** by a `letI` in the body, never resolved: §51 forbids
it being an instance, because at a loop orbit it and `edgeRightAlgebra` inhabit the same type with
different content.  This is `CONVENTIONS.md` §3's branch-(iii) remedy applied structurally — the
transport is paid **once, in a named definition**, and every use site inherits the right structure
by construction rather than by hoping synthesis picks it.

An `abbrev`, so the `letI` unfolds and the elaborated type is the honest tensor product.

@census none (helper for `RQ2-2.20-C2`) -/
noncomputable abbrev edgeSummand (M : Rep Γ) {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) :
    Type u :=
  edgeSummandG ↥(M.vertexFixed (Γ.vertexRep i)) ε

/-- **`RQ2-2.20` item 2, second half — the splitting.**
`{}_iM_j ⊗_{L_i} W_i  ≅  ∏_ε (L(e_ε) ⊗_{L_i,σ_ε} W_i)`.

Mathlib's `TensorProduct.piLeft` does it, and the only thing needed to *reach* it is
`edgeLeftAlgebraSpecies_smul_apply` — the `rfl` saying that `{}_iM_j`'s `L_i`-action is
`edgeLeftAlgebra` factor by factor.  So the `σ_ε` twists of `eq:edgediagram`'s left half are
already sitting on the summands the moment the product splits; nothing puts them there.

`Finite (Γ.EdgeOrbit i j)` comes from `RQ2-1.01-H2` by `infer_instance` (§50 (a)); `piLeft` wants
`Fintype`, which is `Fintype.ofFinite`.

@census none (clause witness for `RQ2-2.20-C2`) -/
noncomputable def piSplit (M : Rep Γ) (i j : Γ.VertexOrbit) :
    (Γ.toSpecies.M i j ⊗[Γ.toSpecies.L i] ↥(M.vertexFixed (Γ.vertexRep i)))
      ≃ₗ[Γ.toSpecies.L i] (∀ ε : Γ.EdgeOrbit i j, edgeSummand M ε) := by
  classical
  letI : Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
  letI : ∀ ε : Γ.EdgeOrbit i j, Module (Γ.toSpecies.L i) ↥(Γ.edgeOrbitField ε) :=
    fun ε => (edgeLeftAlgebraSpecies ε).toModule
  exact TensorProduct.piLeft _ _ _

/-- The splitting on a pure tensor: `m ⊗ w ↦ (m_ε ⊗ w)_ε`.
@census none (helper for `RQ2-2.20-C2`) -/
@[simp] theorem piSplit_tmul (M : Rep Γ) (i j : Γ.VertexOrbit)
    (m : Γ.toSpecies.M i j) (w : ↥(M.vertexFixed (Γ.vertexRep i)))
    (ε : Γ.EdgeOrbit i j) :
    piSplit M i j (m ⊗ₜ[Γ.toSpecies.L i] w) ε
      = (letI := edgeLeftAlgebraSpecies ε; (m ε) ⊗ₜ[Γ.toSpecies.L i] w) := by
  classical
  letI : Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
  letI : ∀ ε : Γ.EdgeOrbit i j, Module (Γ.toSpecies.L i) ↥(Γ.edgeOrbitField ε) :=
    fun ε => (edgeLeftAlgebraSpecies ε).toModule
  show TensorProduct.piLeft _ _ _ (m ⊗ₜ[Γ.toSpecies.L i] w) ε = _
  simp [TensorProduct.piLeft, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]

/-! ### `RQ2-2.20` item 5: cancelling `L(e_ε)` and composing the twists

The per-`(ε, η)` step: `RQ2-2.19` hands back
`Twist(L(e_ε), ρ) ⊗_{TwistBase} (L(e_ε) ⊗_{L_i,σ_ε} W_i)` with `ρ = ητ_ε⁻¹`, and the row wants
`Twist(L(v_i), ρσ_ε) ⊗_{TwistBase} W_i`.  So `L(e_ε)` has to be cancelled and the two twists
composed into one.

**The conjugation order does not apply here, and the reason is worth recording.**  §'s pattern —
distribute on the honest *untwisted* object, restore the twist last — needs an untwisted object to
work on.  Here there is none: `cancelBaseChange` at `R := L_i`, `A := L(e_ε)`, `M := L` demands
`IsScalarTower L_i (L(e_ε)) L`, which unfolds to `σ_ε(b)·x·a = b·x·a` — **false**, and false by
exactly `σ_ε`.  The cancellation is possible only if the carrier already has its `L_i`-structure
*through* `σ_ε`, i.e. only on a `Twist`.  So the twist cannot be removed before the cancellation;
it is what makes the cancellation typecheck.

**That is fidelity evidence, from an unexpected direction.**  The source writes the summand's
twist as `η τ_ε⁻¹ σ_ε`.  The `σ_ε` in it is not a decoration and not a convention: it is the tower
obstruction to cancelling `L(e_ε)`, made into data.  The frozen statement is re-derived here from
the construction's own constraints.

The map is therefore built **directly**, in one step, on generators —
`t ⊗ (x ⊗ w) ↦ ofL (t.val · ρ(x)) ⊗ w` — which is `cancelBaseChange`'s own formula with the two
twists already composed.  Bijection first, `L`-linearity from the pin, as in `RQ2-2.19`.

@census none (G4 engine for `RQ2-2.20-C1`)
-/

/-- **`RQ2-2.19`'s `hVT`, discharged for the summand** — by `rfl`, because
`moduleTwistBase_edgeSummandG` is `compHom toE` by construction.  This is finding **S5-F6**'s
hypothesis being paid at the only place that owes it, and paying nothing.

*The three instances this used to be accompanied by are gone*: they are
`moduleEdgeField_edgeSummandG`, `moduleTwistBase_edgeSummandG` and `moduleVOFj_edgeSummandG`,
keyed to the generic carrier, and `edgeSummand M ε` reduces to `edgeSummandG _ ε`.  Keeping
specialised copies would have put two instances of one class at one head — §51's rule, one level
out.

@census none (helper for `RQ2-2.20-C1`) -/
theorem twistBase_smul_edgeSummand (M : Rep Γ) {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (ρ : Gal(L/K)) (b : Twist.TwistBase (Γ.edgeOrbitField ε) ρ) (s : edgeSummand M ε) :
    b • s = (b.val : ↥(Γ.edgeOrbitField ε)) • s := rfl

/-- A pure tensor of the summand, named so that `letI`-scoped instances need not be re-entered at
every use.  @census none (helper) -/
noncomputable def edgeSummandMk (M : Rep Γ) {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (x : ↥(Γ.edgeOrbitField ε)) (w : ↥(M.vertexFixed (Γ.vertexRep i))) : edgeSummand M ε :=
  edgeSummandMkG ↥(M.vertexFixed (Γ.vertexRep i)) ε x w

/-- `L(e_ε)` acts on the summand through its left factor, on the nose.  @census none (helper) -/
theorem edgeField_smul_edgeSummandMk (M : Rep Γ) {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (y x : ↥(Γ.edgeOrbitField ε)) (w : ↥(M.vertexFixed (Γ.vertexRep i))) :
    y • edgeSummandMk M ε x w = edgeSummandMk M ε (y * x) w := rfl


/-- `L` as an `L_i`-**algebra** at the species head — the seventh head bridge, and the one that
makes `algebraMap (Γ.toSpecies.L i) L` available as the coercion.  `Species.L` is an abstract
`Type` field, so `IntermediateField`'s own coercion is invisible through the projection; this is
that `S5-F3` boundary in its smallest form.  @census none (helper, `S5-F3`) -/
noncomputable instance algebraSpeciesL (i : Γ.VertexOrbit) : Algebra (Γ.toSpecies.L i) L :=
  inferInstanceAs (Algebra ↥(stabField K L (Γ.vertexRep i)) L)

/-- `edgeComponentLeft_coe_sigma` at the species head.  @census none (helper, `S5-F3`) -/
theorem edgeComponentLeft_coe_sigma_species {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (b : Γ.toSpecies.L i) :
    ((Γ.edgeComponentLeft ε b : ↥(Γ.edgeOrbitField ε)) : L)
      = ch.σ (algebraMap (Γ.toSpecies.L i) L b) :=
  edgeComponentLeft_coe_sigma ch b

/-- **The forward map's inner half**, for a fixed `t`: `x ⊗ w ↦ ofL (t.val · ρ(x)) ⊗ w`.

The `L_i`-balance is the whole content, and it is where `σ_ε` enters: `c • x` is
`edgeComponentLeft c · x = σ_ε(c)·x` (`edgeComponentLeft_coe_sigma_species`), so the left side
picks up `ρ(σ_ε(c))`; the right side moves `c` across the target's tensor, where the respelled
base acts by `ρσ_ε`. The two agree because `(ρ ∘ σ_ε)(c) = ρ(σ_ε(c))` — which is precisely why the
row's twist is `η τ_ε⁻¹ σ_ε` and not `η τ_ε⁻¹`.

@census none (helper for `RQ2-2.20-C1`) -/
noncomputable def edgeCancelInner (M : Rep Γ) {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (ch : Γ.EdgeChoice ε) (ρ : Gal(L/K)) (t : Twist (Γ.edgeOrbitField ε) ρ) :
    edgeSummand M ε →+
      (Twist (Γ.vertexOrbitField i) (ρ * ch.σ)
        ⊗[Twist.TwistBase (Γ.vertexOrbitField i) (ρ * ch.σ)] ↥(M.vertexFixed (Γ.vertexRep i))) := by
  letI := edgeLeftAlgebraSpecies ε
  refine TensorProduct.liftAddHom
    ({ toFun := fun x =>
        { toFun := fun w =>
            (Twist.ofL (t.val * ρ ((x : ↥(Γ.edgeOrbitField ε)) : L)))
              ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i) (ρ * ch.σ)] w
          map_zero' := TensorProduct.tmul_zero _ _
          map_add' := fun _ _ => TensorProduct.tmul_add _ _ _ }
       map_zero' := by
         ext w
         show (Twist.ofL (t.val * ρ (((0 : ↥(Γ.edgeOrbitField ε))) : L))) ⊗ₜ _ = 0
         rw [show (((0 : ↥(Γ.edgeOrbitField ε))) : L) = 0 from rfl, map_zero, mul_zero]
         exact TensorProduct.zero_tmul _ _
       map_add' := fun x y => by
         ext w
         show (Twist.ofL (t.val * ρ (((x + y : ↥(Γ.edgeOrbitField ε))) : L))) ⊗ₜ _ = _ + _
         rw [show (((x + y : ↥(Γ.edgeOrbitField ε))) : L) = (x : L) + (y : L) from rfl,
           map_add, mul_add]
         exact TensorProduct.add_tmul _ _ _ }) ?_
  intro c x w
  show (Twist.ofL (t.val * ρ ((((c • x : ↥(Γ.edgeOrbitField ε)))) : L))) ⊗ₜ _
    = (Twist.ofL (t.val * ρ ((x : ↥(Γ.edgeOrbitField ε)) : L))) ⊗ₜ (c • w)
  have hcx : (((c • x : ↥(Γ.edgeOrbitField ε))) : L) = ch.σ (algebraMap (Γ.toSpecies.L i) L c) * (x : L) := by
    show ((Γ.edgeComponentLeft ε c : ↥(Γ.edgeOrbitField ε)) : L) * (x : L) = _
    rw [edgeComponentLeft_coe_sigma_species ch c]
  have hcw : (c • w : ↥(M.vertexFixed (Γ.vertexRep i)))
      = (Twist.TwistBase.ofE c : Twist.TwistBase (Γ.vertexOrbitField i) (ρ * ch.σ)) • w := rfl
  rw [hcx, hcw, ← TensorProduct.smul_tmul, Twist.smul_base_def]
  congr 1
  apply Twist.val_injective
  show t.val * ρ (ch.σ (algebraMap (Γ.toSpecies.L i) L c) * (x : L))
    = (ρ * ch.σ) (algebraMap (Γ.toSpecies.L i) L c)
        * (t.val * ρ ((x : ↥(Γ.edgeOrbitField ε)) : L))
  rw [map_mul, AlgEquiv.mul_apply]
  ring

section Item5

variable (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
  (ch : Γ.EdgeChoice ε) (ρ : Gal(L/K))

/-- The `(ε, η)`-summand the row asks for: `Twist(L(v_i), ρσ_ε) ⊗_{TwistBase} W_i`.
@census none (helper for `RQ2-2.20-C1`) -/
abbrev cancelTarget : Type u :=
  Twist (Γ.vertexOrbitField i) (ρ * ch.σ)
    ⊗[Twist.TwistBase (Γ.vertexOrbitField i) (ρ * ch.σ)] ↥(M.vertexFixed (Γ.vertexRep i))

/-- `edgeCancelInner` on a generator, by `rfl`.  @census none (helper) -/
theorem edgeCancelInner_mk (t : Twist (Γ.edgeOrbitField ε) ρ)
    (x : ↥(Γ.edgeOrbitField ε)) (w : ↥(M.vertexFixed (Γ.vertexRep i))) :
    edgeCancelInner M ε ch ρ t (edgeSummandMk M ε x w)
      = (Twist.ofL (t.val * ρ (x : L))) ⊗ₜ w := rfl

/-- **`RQ2-2.20` item 5, the forward map.**
`t ⊗ (x ⊗ w) ↦ ofL (t.val · ρ(x)) ⊗ w` — `cancelBaseChange`'s formula with the two twists already
composed, since (see the section header) they cannot be composed after the fact.

The outer balance, over `TwistBase(L(e_ε), ρ)`, is where `hVT` is spent: `b • (x ⊗ w)` is
`(b.val · x) ⊗ w` by `twistBase_smul_edgeSummand` (which is `rfl`), and both sides then read
`ofL (ρ(b.val)·t.val·ρ(x)) ⊗ w`.

@census none (helper for `RQ2-2.20-C1`) -/
noncomputable def edgeCancelFwd :
    (Twist (Γ.edgeOrbitField ε) ρ ⊗[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummand M ε)
      →+ cancelTarget M ch ρ := by
  refine TensorProduct.liftAddHom
    ({ toFun := fun t => edgeCancelInner M ε ch ρ t
       map_zero' := by
         refine AddMonoidHom.ext fun s => ?_
         induction s using TensorProduct.induction_on with
         | zero => simp
         | tmul x w =>
             show edgeCancelInner M ε ch ρ 0 (edgeSummandMk M ε x w) = 0
             rw [edgeCancelInner_mk]
             show (Twist.ofL ((0 : Twist (Γ.edgeOrbitField ε) ρ).val * ρ (x : L))) ⊗ₜ w = 0
             rw [show ((0 : Twist (Γ.edgeOrbitField ε) ρ).val) = 0 from rfl, zero_mul]
             exact TensorProduct.zero_tmul _ _
         | add p q hp hq => simp only [map_add, hp, hq, AddMonoidHom.zero_apply, add_zero]
       map_add' := fun t t' => by
         refine AddMonoidHom.ext fun s => ?_
         induction s using TensorProduct.induction_on with
         | zero => simp
         | tmul x w =>
             show edgeCancelInner M ε ch ρ (t + t') (edgeSummandMk M ε x w) = _
             rw [edgeCancelInner_mk]
             show (Twist.ofL ((t + t').val * ρ (x : L))) ⊗ₜ w
               = edgeCancelInner M ε ch ρ t (edgeSummandMk M ε x w)
                 + edgeCancelInner M ε ch ρ t' (edgeSummandMk M ε x w)
             rw [edgeCancelInner_mk, edgeCancelInner_mk,
               show ((t + t').val) = t.val + t'.val from rfl, add_mul]
             exact TensorProduct.add_tmul _ _ _
         | add p q hp hq => simp only [map_add, hp, hq, AddMonoidHom.add_apply] }) ?_
  intro b t s
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul x w =>
      show edgeCancelInner M ε ch ρ (b • t) (edgeSummandMk M ε x w)
        = edgeCancelInner M ε ch ρ t (b • edgeSummandMk M ε x w)
      rw [twistBase_smul_edgeSummand, edgeField_smul_edgeSummandMk,
        edgeCancelInner_mk, edgeCancelInner_mk]
      congr 1
      apply Twist.val_injective
      show (b • t).val * ρ (x : L) = t.val * ρ (((b.val * x : ↥(Γ.edgeOrbitField ε))) : L)
      rw [Twist.val_smulL_base,
        show (((b.val * x : ↥(Γ.edgeOrbitField ε))) : L)
          = ((b.val : ↥(Γ.edgeOrbitField ε)) : L) * (x : L) from rfl, map_mul]
      ring
  | add p q hp hq => simp only [smul_add, map_add, hp, hq]


/-- The forward map on a generator, by `rfl` — the pin the round trips and the row's `C1` consume.
@census none (helper for `RQ2-2.20-C1`) -/
theorem edgeCancelFwd_mk (t : Twist (Γ.edgeOrbitField ε) ρ)
    (x : ↥(Γ.edgeOrbitField ε)) (w : ↥(M.vertexFixed (Γ.vertexRep i))) :
    edgeCancelFwd M ch ρ (t ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandMk M ε x w)
      = (Twist.ofL (t.val * ρ (x : L))) ⊗ₜ w := rfl

/-- A generator of the summand as `L(e_ε)` acting on `1 ⊗ w`.  @census none (helper) -/
theorem edgeSummandMk_eq_smul_one (y : ↥(Γ.edgeOrbitField ε))
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) :
    edgeSummandMk M ε y w = y • edgeSummandMk M ε 1 w := by
  rw [edgeField_smul_edgeSummandMk, mul_one]

/-- A generator of the summand as the respelled base acting on `1 ⊗ w`.  The scalar is moved into
`TwistBase E ρ` — the tensor's **own** base ring — rather than left in `↥E`: `TensorProduct.smul_tmul`
across a *different* ring would want `CompatibleSMul`, which does not hold here.
@census none (helper) -/
theorem edgeSummandMk_eq_twistBase_smul_one (y : ↥(Γ.edgeOrbitField ε))
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) :
    edgeSummandMk M ε y w
      = (Twist.TwistBase.ofE y : Twist.TwistBase (Γ.edgeOrbitField ε) ρ)
          • edgeSummandMk M ε 1 w := by
  rw [twistBase_smul_edgeSummand]
  exact edgeSummandMk_eq_smul_one M y w

/-- `1 ⊗ (c • w) = σ_ε(c) ⊗ w`: moving an `L_i`-scalar to the left factor turns it into
`edgeComponentLeft c`.  Stated wholly at the **species** head, which is where `edgeSummand`'s
tensor lives.  @census none (helper) -/
theorem edgeSummandMk_one_smul (c : Γ.toSpecies.L i)
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) :
    edgeSummandMk M ε 1 (c • w) = edgeSummandMk M ε (Γ.edgeComponentLeft ε c) w := by
  letI := edgeLeftAlgebraSpecies ε
  show (1 : ↥(Γ.edgeOrbitField ε)) ⊗ₜ[Γ.toSpecies.L i] (c • w)
    = (Γ.edgeComponentLeft ε c) ⊗ₜ[Γ.toSpecies.L i] w
  rw [← TensorProduct.smul_tmul]
  congr 1
  show (Γ.edgeComponentLeft ε c) * 1 = Γ.edgeComponentLeft ε c
  rw [mul_one]


/-- **The inverse**, `s ⊗ w ↦ ofL s.val ⊗ (1 ⊗ w)`.

Its balance mirrors the forward one: `1 ⊗ (b.val • w)` becomes `σ_ε(b.val) ⊗ w`
(`edgeSummandMk_one_smul`), and moving that scalar across the outer tensor multiplies the carrier
by `ρ(σ_ε(b.val)) = (ρσ_ε)(b.val)` — the same composite, met from the other side.

@census none (helper for `RQ2-2.20-C1`) -/
noncomputable def edgeCancelBwd :
    cancelTarget M ch ρ →+
      (Twist (Γ.edgeOrbitField ε) ρ ⊗[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummand M ε) := by
  letI := edgeLeftAlgebraSpecies ε
  refine TensorProduct.liftAddHom
    ({ toFun := fun s =>
        { toFun := fun w =>
            (Twist.ofL s.val : Twist (Γ.edgeOrbitField ε) ρ)
              ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandMk M ε 1 w
          map_zero' := by
            show _ ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ]
              edgeSummandMk M ε 1 (0 : ↥(M.vertexFixed (Γ.vertexRep i))) = 0
            rw [show edgeSummandMk M ε (1 : ↥(Γ.edgeOrbitField ε))
                  (0 : ↥(M.vertexFixed (Γ.vertexRep i))) = 0 from
                TensorProduct.tmul_zero _ _]
            exact TensorProduct.tmul_zero _ _
          map_add' := fun w w' => by
            show _ ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ]
              edgeSummandMk M ε 1 (w + w') = _
            rw [show edgeSummandMk M ε (1 : ↥(Γ.edgeOrbitField ε)) (w + w')
                  = edgeSummandMk M ε 1 w + edgeSummandMk M ε 1 w' from
                TensorProduct.tmul_add _ _ _]
            exact TensorProduct.tmul_add _ _ _ }
       map_zero' := by
         refine AddMonoidHom.ext fun w => ?_
         show (Twist.ofL ((0 : Twist (Γ.vertexOrbitField i) (ρ * ch.σ)).val)
             : Twist (Γ.edgeOrbitField ε) ρ)
             ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandMk M ε 1 w = 0
         rw [show ((0 : Twist (Γ.vertexOrbitField i) (ρ * ch.σ)).val) = 0 from rfl]
         exact TensorProduct.zero_tmul _ _
       map_add' := fun s s' => by
         refine AddMonoidHom.ext fun w => ?_
         show (Twist.ofL ((s + s').val) : Twist (Γ.edgeOrbitField ε) ρ)
             ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandMk M ε 1 w
           = (Twist.ofL s.val : Twist (Γ.edgeOrbitField ε) ρ)
               ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandMk M ε 1 w
             + (Twist.ofL s'.val : Twist (Γ.edgeOrbitField ε) ρ)
               ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandMk M ε 1 w
         rw [show (Twist.ofL ((s + s').val) : Twist (Γ.edgeOrbitField ε) ρ)
               = (Twist.ofL s.val : Twist (Γ.edgeOrbitField ε) ρ)
                 + (Twist.ofL s'.val : Twist (Γ.edgeOrbitField ε) ρ) from rfl]
         exact TensorProduct.add_tmul _ _ _ }) ?_
  intro b s w
  show (Twist.ofL ((b • s).val) : Twist (Γ.edgeOrbitField ε) ρ)
      ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandMk M ε 1 w
    = (Twist.ofL s.val : Twist (Γ.edgeOrbitField ε) ρ)
      ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandMk M ε 1 (b • w)
  have hbw : edgeSummandMk M ε 1 (b • w)
      = edgeSummandMk M ε (Γ.edgeComponentLeft ε b.val) w :=
    edgeSummandMk_one_smul M b.val w
  rw [hbw, edgeSummandMk_eq_twistBase_smul_one (ρ := ρ) (y := Γ.edgeComponentLeft ε b.val),
    ← TensorProduct.smul_tmul, Twist.smul_base_def]
  congr 1
  apply Twist.val_injective
  show (b • s).val
    = ρ ((Γ.edgeComponentLeft ε b.val : ↥(Γ.edgeOrbitField ε)) : L) * s.val
  rw [Twist.val_smulL_base, edgeComponentLeft_coe_sigma_species ch, AlgEquiv.mul_apply]
  rfl

/-- The inverse on a generator.  @census none (helper) -/
theorem edgeCancelBwd_mk (s : Twist (Γ.vertexOrbitField i) (ρ * ch.σ))
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) :
    edgeCancelBwd M ch ρ (s ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i) (ρ * ch.σ)] w)
      = (Twist.ofL s.val : Twist (Γ.edgeOrbitField ε) ρ)
          ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandMk M ε 1 w := by
  letI := edgeLeftAlgebraSpecies ε
  rfl


/-- **`RQ2-2.20` item 5, complete**: `L(e_ε)` cancelled and the two twists composed.

`Twist(L(e_ε), ρ) ⊗_{TwistBase} (L(e_ε) ⊗_{L_i,σ_ε} W_i)  ≃+  Twist(L(v_i), ρσ_ε) ⊗_{TwistBase} W_i`

An `AddEquiv`, per the stage's thrice-used discipline: build the bijection, recover linearity from
the pin (`edgeCancel_apply`) where the assembly needs it.  Both round trips reduce, on generators,
to moving one scalar across one tensor — forwards `edgeSummandMk x w = ofE x • edgeSummandMk 1 w`,
backwards `ρ(1) = 1`.

@census none (helper for `RQ2-2.20-C1`) -/
noncomputable def edgeCancel :
    (Twist (Γ.edgeOrbitField ε) ρ ⊗[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummand M ε)
      ≃+ cancelTarget M ch ρ where
  toFun := edgeCancelFwd M ch ρ
  invFun := edgeCancelBwd M ch ρ
  map_add' := map_add _
  left_inv z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul t s =>
        induction s using TensorProduct.induction_on with
        | zero => simp
        | tmul x w =>
            show edgeCancelBwd M ch ρ (edgeCancelFwd M ch ρ
              (t ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandMk M ε x w)) = _
            rw [edgeCancelFwd_mk, edgeCancelBwd_mk]
            show (Twist.ofL ((Twist.ofL (t.val * ρ (x : L))
                : Twist (Γ.edgeOrbitField ε) ρ).val) : Twist (Γ.edgeOrbitField ε) ρ)
                ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandMk M ε 1 w
              = t ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandMk M ε x w
            rw [edgeSummandMk_eq_twistBase_smul_one (ρ := ρ) (y := x), ← TensorProduct.smul_tmul,
              Twist.smul_base_def]
            congr 1
            apply Twist.val_injective
            show t.val * ρ (x : L) = ρ ((x : ↥(Γ.edgeOrbitField ε)) : L) * t.val
            ring
        | add p q hp hq =>
            rw [show t ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] (p + q)
                = t ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] p
                  + t ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] q from
              TensorProduct.tmul_add _ _ _, map_add, map_add, hp, hq]
    | add p q hp hq => rw [map_add, map_add, hp, hq]
  right_inv y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
        show edgeCancelFwd M ch ρ (edgeCancelBwd M ch ρ
          (s ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i) (ρ * ch.σ)] w)) = _
        rw [edgeCancelBwd_mk, edgeCancelFwd_mk]
        congr 1
        apply Twist.val_injective
        show (Twist.ofL s.val : Twist (Γ.edgeOrbitField ε) ρ).val
            * ρ (((1 : ↥(Γ.edgeOrbitField ε))) : L) = s.val
        rw [show (((1 : ↥(Γ.edgeOrbitField ε))) : L) = 1 from rfl, map_one, mul_one]
    | add p q hp hq => rw [map_add, map_add, hp, hq]

/-- The pin: `t ⊗ (x ⊗ w) ↦ ofL (t.val · ρ(x)) ⊗ w`, by `rfl`.
@census none (helper for `RQ2-2.20-C1`) -/
@[simp] theorem edgeCancel_apply (t : Twist (Γ.edgeOrbitField ε) ρ)
    (x : ↥(Γ.edgeOrbitField ε)) (w : ↥(M.vertexFixed (Γ.vertexRep i))) :
    edgeCancel M ch ρ (t ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandMk M ε x w)
      = (Twist.ofL (t.val * ρ (x : L))) ⊗ₜ w := rfl

/-- **`RQ2-2.19`'s `hV`, discharged for the summand** — by `rfl`, because the `L_j`-action
(`moduleVOFj_edgeSummandG`, keyed to the generic carrier) is *defined* through
`edgeComponentRight`.  That is `eq:edgediagram`'s **right** half, the mirror of the `σ_ε` the
summand already carries on the left.  @census none (helper for `RQ2-2.20-C1`) -/
theorem hV_edgeSummand (a : ↥(Γ.vertexOrbitField j)) (v : edgeSummand M ε) :
    a • v = (Γ.edgeComponentRight ε a) • v := rfl


/-- **`RQ2-2.19` consumed.**  The row proved at `4e38c84`, applied per edge orbit at
`V := L(e_ε) ⊗_{L_i,σ_ε} W_i`.

Both of its hypotheses are discharged by `rfl`: `hV` by `hV_edgeSummand` (the `L_j`-action is
*defined* through `edgeComponentRight`) and `hVT` by `twistBase_smul_edgeSummand` (the respelled
base acts through `toE` by construction).  The `hVT` that finding **S5-F6** added to the row costs
its only consumer nothing, exactly as §48 predicted when the repair was proposed — this is that
prediction discharged rather than restated.

@census none (helper for `RQ2-2.20-C1`) -/
theorem leEpsilon_at_edgeSummand (ch : Γ.EdgeChoice ε) :
    ∃ e : (L ⊗[↥(Γ.vertexOrbitField j)] edgeSummand M ε) ≃ₗ[L]
        (∀ η : EdgeChoice.CosetIndex Γ ch,
          Twist (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)
            ⊗[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)]
              edgeSummand M ε),
      ∀ (a : L) (v : edgeSummand M ε) (η : EdgeChoice.CosetIndex Γ ch),
        e (a ⊗ₜ[↥(Γ.vertexOrbitField j)] v) η
          = Twist.ofL a
              ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ ch η * ch.τ⁻¹)] v :=
  Γ.leEpsilon_decomposition ch (edgeSummand M ε) (hV_edgeSummand M)
    (fun τ => twistBase_smul_edgeSummand M ε τ)

/-- **`edgeCancel`, upgraded to `L`-linear** — recovered from its pin, not from its links.

`L` acts on both sides through the `Twist` carrier, and on a generator the pin gives
`ofL ((c·t.val)·ρ(x)) ⊗ w` on one side and `c • (ofL (t.val·ρ(x)) ⊗ w)` on the other; `mul_assoc`
finishes it.  This is the stage's bijection-then-recover-linearity split used a fourth time, and
it is why `edgeCancel` was built as an `AddEquiv` in the first place.

@census none (helper for `RQ2-2.20-C1`) -/
noncomputable def edgeCancelL :
    (Twist (Γ.edgeOrbitField ε) ρ ⊗[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummand M ε)
      ≃ₗ[L] cancelTarget M ch ρ :=
  AddEquiv.toLinearEquiv (edgeCancel M ch ρ) (fun c z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul t s =>
        induction s using TensorProduct.induction_on with
        | zero => simp
        | tmul x w =>
            show edgeCancel M ch ρ ((c • t)
                ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandMk M ε x w)
              = c • (edgeCancel M ch ρ
                  (t ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] edgeSummandMk M ε x w))
            rw [edgeCancel_apply, edgeCancel_apply]
            show (Twist.ofL ((c • t).val * ρ (x : L)))
                ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i) (ρ * ch.σ)] w
              = c • ((Twist.ofL (t.val * ρ (x : L)))
                ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i) (ρ * ch.σ)] w)
            rw [TensorProduct.smul_tmul']
            congr 1
            apply Twist.val_injective
            show (c • t).val * ρ (x : L) = c * (t.val * ρ (x : L))
            rw [show ((c • t).val) = c * t.val from rfl, mul_assoc]
        | add p q hp hq =>
            rw [show t ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] (p + q)
                = t ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] p
                  + t ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) ρ] q from
              TensorProduct.tmul_add _ _ _, smul_add, map_add, map_add, hp, hq, smul_add]
    | add p q hp hq => rw [smul_add, map_add, map_add, hp, hq, smul_add])

end Item5

/-! ### `RQ2-2.20` item 3: the outer base change, as a mathlib tensor

`Balanced.equivTensor` (`Species/Rep/Tensor.lean`) identifies the outer
`(W_i ⊗_{L_i} {}_iM_j) ⊗_{L_j} L` with mathlib's `L ⊗[L_j] (W_i ⊗_{L_i} {}_iM_j)`, which is the
shape `RQ2-2.19` is stated in.  Two carrier-keyed instances are all it needs.

**Keyed to the carrier, per `CONVENTIONS.md` §3.**  `moduleOfOpposite` is deliberately *not* an
instance — as an ambient one its head is `Module ?A ?X` with both arguments variable and instance
search cannot afford it (measured: a `synthInstance` timeout plus a spurious
`failed to synthesize Module K L`, at these very heads).  The two instances below name their
carrier, exactly as the six head bridges above and the `moduleTwistBase_*` pair do.

@census none (G4 engine for `RQ2-2.20`)
-/

/-- The **left** `L_j`-structure on `W_i ⊗_{L_i} {}_iM_j`, from its right one (`L_j` is
commutative).  @census none (helper) -/
noncomputable instance moduleSpeciesLj_repTensor (i j : Γ.VertexOrbit) (X : Type u)
    [AddCommGroup X] [Module K X] [Module (Γ.toSpecies.L i)ᵐᵒᵖ X]
    [IsScalarTower K (Γ.toSpecies.L i)ᵐᵒᵖ X] :
    Module (Γ.toSpecies.L j) (EtaleSpecies.Rep.tensor Γ.toSpecies i j X) :=
  moduleOfOpposite _ _

/-- …and its ambient `K`-structure is the induced one.  @census none (helper) -/
instance towerK_speciesLj_repTensor (i j : Γ.VertexOrbit) (X : Type u)
    [AddCommGroup X] [Module K X] [Module (Γ.toSpecies.L i)ᵐᵒᵖ X]
    [IsScalarTower K (Γ.toSpecies.L i)ᵐᵒᵖ X] :
    IsScalarTower K (Γ.toSpecies.L j) (EtaleSpecies.Rep.tensor Γ.toSpecies i j X) where
  smul_assoc c a x := by
    show (MulOpposite.op (c • a)) • x = c • ((MulOpposite.op a) • x)
    rw [← smul_assoc c (MulOpposite.op a) x]
    congr 1

/-- **`RQ2-2.20` item 3.**  `(W_i ⊗_{L_i} {}_iM_j) ⊗_{L_j} L  =  L ⊗_{L_j} (W_i ⊗_{L_i} {}_iM_j)`,
mathlib's spelling on the right — which is the shape `RQ2-2.19` consumes.

`hX` is `rfl`: the left `L_j`-action on the inner product is *defined* as the right one through
`A ≃+* Aᵐᵒᵖ`, so there is nothing to prove and nothing to transport.

@census none (helper for `RQ2-2.20-C1`) -/
noncomputable def outerEquiv (i j : Γ.VertexOrbit) (X : Type u)
    [AddCommGroup X] [Module K X] [Module (Γ.toSpecies.L i)ᵐᵒᵖ X]
    [IsScalarTower K (Γ.toSpecies.L i)ᵐᵒᵖ X] :
    Balanced K (Γ.toSpecies.L j) L L (EtaleSpecies.Rep.tensor Γ.toSpecies i j X)
      ≃ₗ[Lᵐᵒᵖ] (L ⊗[Γ.toSpecies.L j] (EtaleSpecies.Rep.tensor Γ.toSpecies i j X)) :=
  Balanced.equivTensor (B := L) (fun _ _ => rfl)

/-- `outerEquiv` on a pure tensor, by `rfl`.  @census none (helper) -/
@[simp] theorem outerEquiv_mk (i j : Γ.VertexOrbit) (X : Type u)
    [AddCommGroup X] [Module K X] [Module (Γ.toSpecies.L i)ᵐᵒᵖ X]
    [IsScalarTower K (Γ.toSpecies.L i)ᵐᵒᵖ X]
    (t : EtaleSpecies.Rep.tensor Γ.toSpecies i j X) (a : L) :
    outerEquiv i j X (Balanced.mk t a) = a ⊗ₜ[Γ.toSpecies.L j] t := rfl

/-! ### `RQ2-2.20` item 6: getting the chain's links onto one head

The links exist and are each an equivalence, but they are linear over four different rings:
`outerEquiv` over `Lᵐᵒᵖ`, `innerEquiv` over `(L_j)ᵐᵒᵖ`, `piSplit` over `L_i`, and `RQ2-2.19` over
`↥(Γ.vertexOrbitField j)` — whose statement is frozen, so **that** is the head everything must
reach.  `Γ.toSpecies.L j` and `↥(Γ.vertexOrbitField j)` are definitionally equal and instance
search does not know it, so each structure needs re-heading once; the `≃ₗ` upgrades then follow
because `L_j` is commutative and `moduleOfOpposite` makes the two sides agree by `rfl`.

Nothing here is mathematics.  It is the `S5-F3` boundary, and the reason it is cheap is that
`Balanced.equivTensor` and `moduleOfOpposite` already named it once (`MD-S5-07`) — each bridge
below is `inferInstanceAs` or `moduleOfOpposite`, never a construction.

@census none (G4 engine for `RQ2-2.20`)
-/

section Item6

variable (M : Rep Γ) (i j : Γ.VertexOrbit)

/-- `W_i ⊗_{L_i} {}_iM_j` over `L_j` at the **frozen row's** head.  @census none (helper, `S5-F3`) -/
noncomputable instance moduleVOFj_repTensor (X : Type u)
    [AddCommGroup X] [Module K X] [Module (Γ.toSpecies.L i)ᵐᵒᵖ X]
    [IsScalarTower K (Γ.toSpecies.L i)ᵐᵒᵖ X] :
    Module ↥(Γ.vertexOrbitField j) (EtaleSpecies.Rep.tensor Γ.toSpecies i j X) :=
  inferInstanceAs (Module (Γ.toSpecies.L j) _)

/-- `{}_iM_j ⊗[L_i] W_i` over `L_j`, from its right action.  @census none (helper, `S5-F3`) -/
noncomputable instance moduleSpeciesLj_innerTensor :
    Module (Γ.toSpecies.L j)
      (Γ.toSpecies.M i j ⊗[Γ.toSpecies.L i] ↥(M.vertexFixed (Γ.vertexRep i))) :=
  moduleOfOpposite _ _

/-- …re-headed.  @census none (helper, `S5-F3`) -/
noncomputable instance moduleVOFj_innerTensor :
    Module ↥(Γ.vertexOrbitField j)
      (Γ.toSpecies.M i j ⊗[Γ.toSpecies.L i] ↥(M.vertexFixed (Γ.vertexRep i))) :=
  inferInstanceAs (Module (Γ.toSpecies.L j) _)

/-- `{}_iM_j`'s right `L_j`-action at the frozen row's head.  @census none (helper, `S5-F3`) -/
noncomputable instance moduleVOFjOp_speciesM :
    Module (↥(Γ.vertexOrbitField j))ᵐᵒᵖ (Γ.toSpecies.M i j) :=
  inferInstanceAs (Module (Γ.toSpecies.L j)ᵐᵒᵖ _)

/-- `innerEquiv`, upgraded from `(L_j)ᵐᵒᵖ`-linear to `L_j`-linear.  `L_j` is commutative and
`moduleOfOpposite` makes `c • x` and `op c • x` the same term, so the upgrade is the original
`map_smul` read at `op c`.  @census none (helper for `RQ2-2.20-C1`) -/
noncomputable def innerEquivVOF :
    EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
      ≃ₗ[↥(Γ.vertexOrbitField j)]
      (Γ.toSpecies.M i j ⊗[Γ.toSpecies.L i] ↥(M.vertexFixed (Γ.vertexRep i))) :=
  AddEquiv.toLinearEquiv (innerEquiv M i j).toAddEquiv
    (fun c x => by exact (innerEquiv M i j).map_smul (MulOpposite.op c) x)

/-- `piSplit`, upgraded from `L_i`-linear to `L_j`-linear.

This one is a genuine (if short) proof rather than a transport: `L_j` acts on the source through
`{}_iM_j`'s **right** action and on the target componentwise through `edgeComponentRight`, and the
two agree on generators because `piSplit` is `piLeft`, which acts factorwise.  That is
`eq:edgediagram`'s right half surviving the splitting, as its left half did.

@census none (helper for `RQ2-2.20-C2`) -/
noncomputable def piSplitVOF :
    (Γ.toSpecies.M i j ⊗[Γ.toSpecies.L i] ↥(M.vertexFixed (Γ.vertexRep i)))
      ≃ₗ[↥(Γ.vertexOrbitField j)] (∀ ε : Γ.EdgeOrbit i j, edgeSummand M ε) :=
  AddEquiv.toLinearEquiv (piSplit M i j).toAddEquiv (fun c z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m w =>
        funext ε
        show piSplit M i j ((MulOpposite.op c • m) ⊗ₜ[Γ.toSpecies.L i] w) ε
          = c • (piSplit M i j (m ⊗ₜ[Γ.toSpecies.L i] w) ε)
        rw [piSplit_tmul, piSplit_tmul]
        rfl
    | add p q hp hq => rw [smul_add, map_add, map_add, hp, hq, smul_add])

section OuterL

variable (X : Type u) [AddCommGroup X] [Module K X] [Module (Γ.toSpecies.L i)ᵐᵒᵖ X]
  [IsScalarTower K (Γ.toSpecies.L i)ᵐᵒᵖ X]

/-- `outerEquiv` with the scalar tower supplied **positionally**.

`Balanced.equivTensor` needs `IsScalarTower K (L_j) (W_i ⊗_{L_i} {}_iM_j)`.  That instance exists
(`towerK_speciesLj_repTensor`) and `infer_instance` finds it *in isolation* — but synthesis does
not find it inside this elaboration, and a `haveI` supplying it verbatim does not help either.
Supplied by position it is accepted and everything typechecks, so **the term was always correct
and only the search failed**.

Found by compiled comparison rather than by reading a trace: filling the slot and letting the
type mismatch name what Lean actually wanted.  Recorded because the symptom — an instance that
`infer_instance` produces on demand yet synthesis will not find in place — reads as an
incoherence and is not one.

@census none (helper for `RQ2-2.20-C1`) -/
noncomputable def outerEquivMop : Balanced K (Γ.toSpecies.L j) L L
      (EtaleSpecies.Rep.tensor Γ.toSpecies i j X)
    ≃ₗ[Lᵐᵒᵖ] (L ⊗[↥(Γ.vertexOrbitField j)]
      (EtaleSpecies.Rep.tensor Γ.toSpecies i j X)) :=
  @Balanced.equivTensor K _ (Γ.toSpecies.L j) _ _ L _ _ L _ _ _ _ _ _ _ _
    (EtaleSpecies.Rep.tensor Γ.toSpecies i j X) _ _ _ _ _
    (towerK_speciesLj_repTensor i j X) (fun _ _ => rfl)

/-- The mirror bridge on the mathlib-tensor side, by one `mul_comm`.
@census none (helper, `S5-F7`) -/
theorem tensor_smul_L_eq_op_at (c : L)
    (z : L ⊗[↥(Γ.vertexOrbitField j)] (EtaleSpecies.Rep.tensor Γ.toSpecies i j X)) :
    c • z = MulOpposite.op c • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
      show (c • a) ⊗ₜ[↥(Γ.vertexOrbitField j)] t = (MulOpposite.op c • a) ⊗ₜ _
      congr 1
      show c * a = a * c
      exact mul_comm c a
  | add p q hp hq => rw [smul_add, smul_add, hp, hq]

/-- **`outerEquiv`, `L`-linear.**  `RQ2-2.20` item 6's first link, and the last piece the row's
chain was missing.

`L`-linearity is recovered from the two `S5-F7` bridges — possible only because that finding was
normalised at the root (§52.4e); before it, `map_smul`'s obligation and every `•`-lemma were
generated from different `SMul`s.

@census none (helper for `RQ2-2.20-C1`) -/
noncomputable def outerEquivL :
    Balanced K (Γ.toSpecies.L j) L L (EtaleSpecies.Rep.tensor Γ.toSpecies i j X)
      ≃ₗ[L] (L ⊗[↥(Γ.vertexOrbitField j)] (EtaleSpecies.Rep.tensor Γ.toSpecies i j X)) :=
  AddEquiv.toLinearEquiv (outerEquivMop i j X).toAddEquiv (fun c x => by
    exact (congrArg (outerEquivMop i j X).toAddEquiv
        (balanced_smul_L_eq_op (Γ.toSpecies.L j)
          (EtaleSpecies.Rep.tensor Γ.toSpecies i j X) c x)).trans
      (((outerEquivMop i j X).map_smul (MulOpposite.op c) x).trans
        (tensor_smul_L_eq_op_at i j X c _).symm))

end OuterL

end Item6

/-! ### `RQ2-2.20` items 6 and 7: the chain composed, and the canonicity pin

Item 6 is the composition itself.  Every link was built above; all that is left is to name the
order and let each `≃ₗ[L]` compose:

```
Balanced K L_j L L (W_i ⊗_{L_i} {}_iM_j)          -- the row's left-hand side
  --outerEquivL-->        L ⊗_{L(v_j)} (W_i ⊗_{L_i} {}_iM_j)
  --innerEquivVOF-->      L ⊗_{L(v_j)} ({}_iM_j ⊗_{L_i} W_i)
  --piSplitVOF-->         L ⊗_{L(v_j)} (∀ ε, L(e_ε) ⊗_{L_i,σ_ε} W_i)
  --piRight-->            ∀ ε, L ⊗_{L(v_j)} (L(e_ε) ⊗_{L_i,σ_ε} W_i)
  --RQ2-2.19 (per ε)-->    ∀ ε, ∀ η, Twist(L(e_ε), ητ_ε⁻¹) ⊗ (L(e_ε) ⊗_{L_i,σ_ε} W_i)
  --edgeCancelL-->        ∀ ε, ∀ η, Twist(L(v_i), ητ_ε⁻¹σ_ε) ⊗ W_i
  --DirectSum-->          ⊕_ε ∀ η, Twist(L(v_i), ητ_ε⁻¹σ_ε) ⊗ W_i
```

The two middle links are `RQ2-2.19` — the row proved at `4e38c84` — applied edge-orbit-wise, which
is exactly §44's corrected dependency order (`RQ2-2.19 → RQ2-2.20`) discharged.

**Item 7 is `V-S5b-6`, and it is why this section carries a `_apply` lemma.**  §31's condition is
*derivation first*: the pin may only be written once the map exists as a term.  `wiiMjPreChain` is
that term, and `wiiMjPreChain_apply` computes it on the row's generators; the frozen row's `C1`
is then upgraded from `Nonempty` to `∃ e, <that formula>` **from the constructed map**, in the
same commit.  Nothing about the formula was guessed: every factor in it is read off a link.

**Placement is instance-parameterised, per §49.**  `Fintype`/`DecidableEq` on `Γ.EdgeOrbit i j`
arrive as *binders* rather than being resolved here, exactly as `tensorPi_cosetEmb_bijective`
takes its `Finite`: the row instantiates them with `Fintype.ofFinite` (`Finite (Γ.EdgeOrbit i j)`
is `RQ2-1.01-H2`, §50 (a)) and `Classical.decEq`, and this section commits nothing about where it
sits.

@census none (G4 engine for `RQ2-2.20`)
-/

section Item7

variable (M : Rep Γ) (i j : Γ.VertexOrbit)
  [Fintype (Γ.EdgeOrbit i j)] [DecidableEq (Γ.EdgeOrbit i j)]

/-- **`RQ2-2.20` item 6: `eq:WiiMjLpre`'s isomorphism, as the composite of the seven links.**

`e` is the family of `RQ2-2.19` identifications, one per edge orbit — supplied as an argument
rather than chosen here, so that `wiiMjPreChain_apply` below can be stated against *the same*
family the row's proof chooses.

@census none (clause witness for `RQ2-2.20-C1`, `RQ2-2.20-C2`) -/
noncomputable def wiiMjPreChain
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e : ∀ ε : Γ.EdgeOrbit i j,
      (L ⊗[↥(Γ.vertexOrbitField j)] edgeSummand M ε) ≃ₗ[L]
        (∀ η : EdgeChoice.CosetIndex Γ (ch ε),
          Twist (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹)
            ⊗[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹)]
              edgeSummand M ε)) :
    Balanced K (Γ.toSpecies.L j) L L
        (EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i)))
      ≃ₗ[L]
      ⨁ ε : Γ.EdgeOrbit i j,
        (∀ η : EdgeChoice.CosetIndex Γ (ch ε),
          Twist (Γ.vertexOrbitField i)
              (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)
            ⊗[Twist.TwistBase (Γ.vertexOrbitField i)
                (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)]
              ↥(M.vertexFixed (Γ.vertexRep i))) :=
  (outerEquivL i j _).trans <|
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
        ((innerEquivVOF M i j).trans (piSplitVOF M i j))).trans <|
      (TensorProduct.piRight _ _ _ _).trans <|
        (LinearEquiv.piCongrRight e).trans <|
          (LinearEquiv.piCongrRight (fun ε =>
            LinearEquiv.piCongrRight (fun η =>
              edgeCancelL M (ch ε) (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹)))).trans
            (DirectSum.linearEquivFunOnFintype L _ _).symm

/-- **`RQ2-2.20` item 7 (`V-S5b-6`): the composite, computed on the row's generators.**

`W_i ⊗_{L_i} {}_iM_j ⊗_{L_j} L` is generated by `(w ⊗ m) ⊗ a`, and the chain sends it to the
family

`(ε, η) ↦ (a · (η τ_ε⁻¹)(m_ε)) ⊗ w`   in `Twist(L(v_i), η τ_ε⁻¹ σ_ε) ⊗ W_i`.

Every factor is read off a link, in order: `a` survives `outerEquivL` and `piRight`; `m_ε` is
`piSplitVOF`'s component of `{}_iM_j = ∏_ε L(e_ε)`; the twist `η τ_ε⁻¹` applied to it is
`RQ2-2.19`'s pin (`leEpsilon_at_edgeSummand`, whose `e` is the argument `e` here); and the product
`a · (ητ_ε⁻¹)(m_ε)` landing in the `η τ_ε⁻¹ σ_ε`-twist is `edgeCancel_apply`.  This is the
embedding of `c ∈ L(e_ε)` into the `η`-summand's `Twist` that §31 requires to exist as a term
before the pin may be written — it is the map `c ↦ (ητ_ε⁻¹)(c) ⊗ w`, here in the shape the
composite actually produces.

Because `Balanced`'s generators span (`Balanced.hom_ext`, applied at both levels), this formula
determines the isomorphism: that is the sense in which the row's `e` is **canonical**, and it is
what `C1` now asserts instead of a bare `Nonempty`.

@census none (clause witness for `RQ2-2.20-C1`) -/
theorem wiiMjPreChain_apply
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e : ∀ ε : Γ.EdgeOrbit i j,
      (L ⊗[↥(Γ.vertexOrbitField j)] edgeSummand M ε) ≃ₗ[L]
        (∀ η : EdgeChoice.CosetIndex Γ (ch ε),
          Twist (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹)
            ⊗[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹)]
              edgeSummand M ε))
    (he : ∀ (ε : Γ.EdgeOrbit i j) (a : L) (v : edgeSummand M ε)
        (η : EdgeChoice.CosetIndex Γ (ch ε)),
      e ε (a ⊗ₜ[↥(Γ.vertexOrbitField j)] v) η
        = Twist.ofL a
            ⊗ₜ[Twist.TwistBase (Γ.edgeOrbitField ε) (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹)] v)
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) (a : L)
    (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)) :
    wiiMjPreChain M i j ch e (Balanced.mk (Balanced.mk w m) a) ε η
      = Twist.ofL (a * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹) ((m ε : L)))
          ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
              (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)] w := by
  have h0 : (outerEquivL i j ↥(M.vertexFixed (Γ.vertexRep i)))
      (Balanced.mk (Balanced.mk w m) a)
      = a ⊗ₜ[↥(Γ.vertexOrbitField j)]
          (Balanced.mk w m : EtaleSpecies.Rep.tensor Γ.toSpecies i j _) := rfl
  have h1 : ((innerEquivVOF M i j).trans (piSplitVOF M i j))
      (Balanced.mk w m : EtaleSpecies.Rep.tensor Γ.toSpecies i j _)
      = fun ε => edgeSummandMk M ε (m ε) w := by
    funext ε'
    show piSplit M i j (m ⊗ₜ[Γ.toSpecies.L i] w) ε' = _
    rw [piSplit_tmul]
    rfl
  simp only [wiiMjPreChain, LinearEquiv.trans_apply, h0,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, h1,
    TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  show edgeCancelL M (ch ε) (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹)
      ((e ε) (a ⊗ₜ[↥(Γ.vertexOrbitField j)] edgeSummandMk M ε (m ε) w) η) = _
  rw [he ε a (edgeSummandMk M ε (m ε) w) η]
  exact edgeCancel_apply M (ch ε) _ (Twist.ofL a) (m ε) w

end Item7

/-- **Proposition `prop:WiiMjLpre`** (census `RQ2-2.20`).

With `M_K` a `K`-rational representation of `Γ_K` and `W_i = M(v_i)^{G_{v_i}}` (clause
`RQ2-2.20-H1`; `Rep.vertexFixed`), and with `ε` running over `G\E_{ij}` and `η` over a system of
representatives for `G_{v_j}/G_{τ_ε^{-1}e_ε}` (clause `RQ2-2.20-H2`; `Γ.EdgeOrbit i j` and
`EdgeChoice.CosetIndex`), there is a canonical isomorphism of `L`-vector spaces

`W_i ⊗_{L_i} {}_iM_j ⊗_{L_j} L = ⊕_{ε} ∏_{η} M(v_i)^{G_{v_i}} ⊗_{L(v_i), η τ_ε^{-1} σ_ε} L`
  (`eq:WiiMjLpre`, clause `RQ2-2.20-C1`),

with the outer index a **direct sum** over edge orbits and the inner one a **product** over the
coset representatives (clause `RQ2-2.20-C2` — `⨁` outside, `∀` inside, in that orientation).

@census    RQ2-2.20
@source    prop:WiiMjLpre
@clauses   RQ2-2.20-H1, RQ2-2.20-H2, RQ2-2.20-C1, RQ2-2.20-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION on clause `RQ2-2.20-C1`.

**`V-S5b-6` is DISCHARGED here** (§31's scheduled, G4-coupled repair; statement delta in
`DESIGN-NOTES` §24).  `C1` read `Nonempty` while the embedding of `c ∈ L(e_ε)` into the
`η`-summand's `Twist` did not exist as a term, and the source calls `eq:WiiMjLpre`'s isomorphism
**canonical**.  That embedding now exists — it is `wiiMjPreChain`, and `wiiMjPreChain_apply`
computes it on generators — so, per §31's *derivation-then-statement* order, `C1` is upgraded to
`∃ e, <e's value on the generators `(w ⊗ m) ⊗ a`>`, written **from** the constructed map and in
the same commit as the row's proof.  The formula was not guessed: each of its factors is read off
one link of the chain (`wiiMjPreChain_apply`'s docstring names which).  Since `Balanced`'s
generators span (`Balanced.hom_ext`, at both levels), the formula determines `e`, which is the
sense in which the row's isomorphism is canonical.

**JUSTIFIED_REFORMULATION** on this module's two standing presentational points and nothing else:
mathlib's base-change factor order, and the twist
`⊗_{L(v_i), η τ_ε^{-1} σ_ε}` — named *after* the ring, hence on the `L` side — being the
`Twist` wrapper of `Species/Rep/Twist.lean`, whose `smul_def` keeps it visible in the elaborated
signature (finding **S5-F4**).

Clause `C2`'s orientation is **not** a divergence and is deliberately literal: the outer index is
`DirectSum` over `Γ.EdgeOrbit i j` and the inner is a dependent function type over
`EdgeChoice.CosetIndex`. Writing a single `Finsupp`, or exchanging the two, would change the object
— the census marks the distinction clause-critical, and for infinite `G` the inner factor is
genuinely a product.

The choice `ch` of `σ_ε, τ_ε` is quantified as a *family* over `ε`, because the right-hand side
names one twist per `(ε, η)`; that is the source's "for each orbit `ε` we choose", made explicit.

**Proof** — the source's own two steps, and it is `wiiMjPreChain`: `{}_iM_j` splits as
`∏_{ε ∈ G\E_{ij}} L(e_ε)` (`piSplitVOF`, on stage S4's `edgeAlgebra`), and `RQ2-2.19` is then
applied to each summand at `V = L(e_ε) ⊗_{L_i,σ_ε} W_i` (`leEpsilon_at_edgeSummand`), after which
`edgeCancelL` cancels `L(e_ε)` and composes the two twists into the single `η τ_ε⁻¹ σ_ε` the
right-hand side names.

**Placement (§49).**  This row is stated *below* `Item6`/`Item7` rather than at its original
position above them: nine of its ingredients — `outerEquivL`, `innerEquivVOF`, `piSplitVOF` and
`wiiMjPreChain` among them — are declared there, and Lean has no forward references.  The
relocation is certified by the elaborated-signature diff recorded in `DESIGN-NOTES` §54, exactly
as `RQ2-2.19`'s was in §49.1.
-/
theorem wiiMj_baseChange_pre (M : Rep Γ) (i j : Γ.VertexOrbit)
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε) :
    ∃ e :
      Balanced K (Γ.toSpecies.L j) L L
          (EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i)))
        ≃ₗ[L]
        ⨁ ε : Γ.EdgeOrbit i j,
          (∀ η : EdgeChoice.CosetIndex Γ (ch ε),
            Twist (Γ.vertexOrbitField i)
                (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)
              ⊗[Twist.TwistBase (Γ.vertexOrbitField i)
                  (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)]
                ↥(M.vertexFixed (Γ.vertexRep i))),
      ∀ (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) (a : L)
        (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)),
        e (Balanced.mk (Balanced.mk w m) a) ε η
          = Twist.ofL (a * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹) ((m ε : L)))
              ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
                  (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)] w := by
  classical
  letI : Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
  choose e he using fun ε : Γ.EdgeOrbit i j => leEpsilon_at_edgeSummand M (ch ε)
  exact ⟨wiiMjPreChain M i j ch e, wiiMjPreChain_apply M i j ch e he⟩

/-! ### `RQ2-2.22` — `eq:WiiMjL`

Three abbreviations first, so that the statement of `cor:WiiMjL` reads as the source's display
rather than as four lines of tensor notation.  They are `abbrev`s, hence reducible, so the
elaborated types are exactly the ones `RQ2-2.20` above is stated with.
-/

/-- `W_i ⊗_{L_i} {}_iM_j ⊗_{L_j} L`, the common left-hand side of `eq:WiiMjLpre` and `eq:WiiMjL`.

@census none (helper)
-/
noncomputable abbrev wiiMjL (M : Rep Γ) (i j : Γ.VertexOrbit) : Type u :=
  Balanced K (Γ.toSpecies.L j) L L
    (EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i)))

/-- The right-hand side of `eq:WiiMjLpre`: `⊕_ε ∏_η W_i ⊗_{L(v_i), η τ_ε^{-1} σ_ε} L`.

@census none (helper)
-/
noncomputable abbrev wiiMjLpreRhs (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε) : Type u :=
  ⨁ ε : Γ.EdgeOrbit i j, (∀ η : EdgeChoice.CosetIndex Γ (ch ε),
    Twist (Γ.vertexOrbitField i) (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)
      ⊗[Twist.TwistBase (Γ.vertexOrbitField i)
          (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)]
        ↥(M.vertexFixed (Γ.vertexRep i)))

/-- **Blast-radius guard** (finding **V-S5b-12**).  `wiiMjLpreRhs` is the type `IsEdgeDescent` and
`RQ2-2.24` are *written in terms of*, so whether those rows balance over the respelled base is not a
question about their own text — it is settled here, definitionally, and this `rfl` records it.

This is the guard that makes the transitive reach of the `S5-F5` respelling checkable without
reading elaborated types: change the base in `wiiMjLpreRhs` and this breaks, and with it every row
that quantifies over `wiiMjLpreRhs`.

@census none (instance guard) -/
theorem wiiMjLpreRhs_base_guard (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε) :
    wiiMjLpreRhs M ch
      = ⨁ ε : Γ.EdgeOrbit i j, (∀ η : EdgeChoice.CosetIndex Γ (ch ε),
          Twist (Γ.vertexOrbitField i) (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)
            ⊗[Twist.TwistBase (Γ.vertexOrbitField i)
                (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)]
              ↥(M.vertexFixed (Γ.vertexRep i))) := rfl

/-- The right-hand side of `eq:WiiMjL`: `⊕_ε ∏_η M(η τ_ε^{-1} σ_ε v_i)`.

@census none (helper)
-/
noncomputable abbrev wiiMjLRhs (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε) : Type u :=
  ⨁ ε : Γ.EdgeOrbit i j, (∀ η : EdgeChoice.CosetIndex Γ (ch ε), M.M (EdgeChoice.cosetVertex Γ (ch ε) η))

/-- **Corollary `cor:WiiMjL`** (census `RQ2-2.22`).

From `RQ2-2.20` and `RQ2-2.21` (clause `RQ2-2.22-H1`): there are canonical `L`-linear isomorphisms

`ψ_{i,j,ε,η} : M(v_i)^{G_{v_i}} ⊗_{L(v_i), η τ_ε^{-1} σ_ε} L → M(η τ_ε^{-1} σ_ε v_i)`
  (`eq:Llinearisos`, clause `RQ2-2.22-C1`),

and hence, for all `i, j ∈ I`, a canonical isomorphism

`W_i ⊗_{L_i} {}_iM_j ⊗_{L_j} L = ⊕_ε ∏_η M(η τ_ε^{-1} σ_ε v_i)`
  (`eq:WiiMjL`, clause `RQ2-2.22-C2`).

@census    RQ2-2.22
@source    cor:WiiMjL
@clauses   RQ2-2.22-H1, RQ2-2.22-C1, RQ2-2.22-C2
@imports   none
@divergence none.

**Canonicity is the content here** — the census note on `RQ2-2.22-C2` says in as many words that "a
non-canonical bases-and-sums reformulation is a divergence" — so neither isomorphism is left as a
bare `Nonempty`:

* `ψ` is pinned by its value on pure tensors (`a ⊗ m ↦ a · φ_{v_i, ητ_ε⁻¹σ_ε}(m)`), which is
  exactly `RQ2-2.21`'s extension map at `σ := η τ_ε^{-1} σ_ε`, `v := v_i`.  So `C1`'s "canonical"
  is delivered by the same device that delivers `RQ2-2.21-C2`, and the two rows agree by
  construction rather than by coincidence.
* `C2` is pinned as the **composite**: the statement says that for *every* `RQ2-2.20` identification
  `e₀` there is an `e` with `e x ε η = ψ ε η (e₀ x ε η)`.  That is the source's own derivation —
  "we apply Proposition `prop:generalextensionofscalars` to each summand on the right hand side of
  `eq:WiiMjLpre`" — read as a specification of `e` rather than as a proof sketch, and it makes
  `C2`'s isomorphism canonical *relative to* `RQ2-2.20`'s, which is the strongest form available
  while `RQ2-2.20` is itself stated existentially.

The presentational points are `RQ2-2.20`'s and are not repeated: mathlib's factor order, and the
twist named after the ring being the `Twist` wrapper.  Clause `C2`'s `⊕`-outside/`∏`-inside
orientation is again literal.

Proof plan (G4): `ψ ε η` is `RQ2-2.21`'s `e σ` at `σ = η τ_ε^{-1} σ_ε`; `e` is `e₀` followed by
`DirectSum.lmap` of `Pi.congrRight (ψ ε)`.
-/
theorem wiiMj_baseChange (M : Rep Γ) (i j : Γ.VertexOrbit)
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε) :
    ∃ ψ : ∀ (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)),
        (Twist (Γ.vertexOrbitField i)
              (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)
            ⊗[Twist.TwistBase (Γ.vertexOrbitField i)
                (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)]
              ↥(M.vertexFixed (Γ.vertexRep i)))
          ≃ₗ[L] M.M ((EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ) • Γ.vertexRep i),
      (∀ (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)) (a : L)
          (m : ↥(M.vertexFixed (Γ.vertexRep i))),
        ψ ε η (Twist.ofL a ⊗ₜ m)
          = a • M.φ (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ) (Γ.vertexRep i)
                (m : M.M (Γ.vertexRep i))) ∧
      (∀ e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch,
        ∃ e : wiiMjL M i j ≃ₗ[L] wiiMjLRhs M ch,
          ∀ x ε η, e x ε η = ψ ε η (e₀ x ε η)) := by
  classical
  refine ⟨fun ε η => generalExtensionLinearEquiv M (Γ.vertexRep i)
      (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ), fun ε η a m => rfl, ?_⟩
  intro e₀
  refine ⟨e₀.trans (DirectSum.congrLinearEquiv fun ε =>
    LinearEquiv.piCongrRight fun η => generalExtensionLinearEquiv M (Γ.vertexRep i)
      (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)), ?_⟩
  intro x ε η
  rfl

/-! ### `RQ2-2.23` — the rational structure `Θ_{ij}`, and the `AN-27` continuity clause -/

/-- **Well-definedness of `Θ`'s index shuffle.**  `σ ∈ G_{v_j}` carries the `σ⁻¹η`-summand's vertex
to the `η`-summand's.

This is what makes the formula of clause `RQ2-2.23-C1` type-check at all, and it is not formal: it
needs `G_{τ_ε^{-1}e_ε} ⊆ G_{τ_ε^{-1}σ_ε v_i}` — stage S4's `stabilizer_le_source`, the stabilizer
of an edge being contained in that of its source — so that `η ↦ η τ_ε^{-1}σ_ε v_i` is independent
of the coset representative `Quotient.out` happens to pick.

@census none (clause witness for `RQ2-2.23-C1`)
@clauses   RQ2-2.23-C1
-/
theorem EdgeChoice.smul_cosetVertex {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (σ : stabilizer Gal(L/K) (Γ.vertexRep j))
    (η : EdgeChoice.CosetIndex Γ ch) :
    (σ : Gal(L/K)) • EdgeChoice.cosetVertex Γ ch (σ⁻¹ • η)
      = EdgeChoice.cosetVertex Γ ch η := by
  -- The two chosen representatives differ by an element `h` of the stabiliser of
  -- `τ_ε⁻¹ e_ε`, and that stabiliser fixes `τ_ε⁻¹ σ_ε v_i = s(τ_ε⁻¹ e_ε)`
  -- (stage S4's `stabilizer_le_source`).  Everything else is bookkeeping.
  have hmem : (Quotient.out (σ⁻¹ • η))⁻¹ * (σ⁻¹ * Quotient.out η)
      ∈ (stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε)).subgroupOf
          (stabilizer Gal(L/K) (Γ.vertexRep j)) := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' η]
    rfl
  set h : stabilizer Gal(L/K) (Γ.vertexRep j) :=
    (Quotient.out (σ⁻¹ • η))⁻¹ * (σ⁻¹ * Quotient.out η) with hh
  -- `σ · out(σ⁻¹η) = out η · h⁻¹`, as elements of `Gal(L/K)`
  have hgrp : (σ : Gal(L/K)) * ((Quotient.out (σ⁻¹ • η) :
      stabilizer Gal(L/K) (Γ.vertexRep j)) : Gal(L/K))
      = ((Quotient.out η : stabilizer Gal(L/K) (Γ.vertexRep j)) : Gal(L/K))
        * ((h⁻¹ : stabilizer Gal(L/K) (Γ.vertexRep j)) : Gal(L/K)) := by
    have : (Quotient.out (σ⁻¹ • η)) * h = σ⁻¹ * Quotient.out η := by
      rw [hh]; group
    have h3 : σ * (Quotient.out (σ⁻¹ • η) * h) = Quotient.out η := by
      rw [this, ← mul_assoc, mul_inv_cancel, one_mul]
    have h4 : σ * Quotient.out (σ⁻¹ • η) = Quotient.out η * h⁻¹ := by
      rw [← h3, mul_assoc, mul_inv_cancel_right]
    exact congrArg (fun t : stabilizer Gal(L/K) (Γ.vertexRep j) => (t : Gal(L/K))) h4
  -- `h⁻¹` fixes `s(τ_ε⁻¹ e_ε) = τ_ε⁻¹ σ_ε v_i`
  have hfix : ((h⁻¹ : stabilizer Gal(L/K) (Γ.vertexRep j)) : Gal(L/K))
      • ((ch.τ⁻¹ * ch.σ) • Γ.vertexRep i) = (ch.τ⁻¹ * ch.σ) • Γ.vertexRep i := by
    have hsrc : (ch.τ⁻¹ * ch.σ) • Γ.vertexRep i
        = Γ.toRQuiver.source (ch.τ⁻¹ • Γ.edgeRep ε) := by
      rw [mul_smul, ch.source_eq, Γ.source_smul]
    rw [hsrc]
    exact Γ.stabilizer_le_source _ ((Subgroup.mem_subgroupOf).mp (inv_mem hmem))
  -- assemble
  show (σ : Gal(L/K)) • ((EdgeChoice.rep Γ ch (σ⁻¹ • η) * ch.τ⁻¹ * ch.σ) • Γ.vertexRep i)
    = (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ) • Γ.vertexRep i
  rw [← mul_smul]
  show ((σ : Gal(L/K)) * (((Quotient.out (σ⁻¹ • η) :
      stabilizer Gal(L/K) (Γ.vertexRep j)) : Gal(L/K)) * ch.τ⁻¹ * ch.σ)) • Γ.vertexRep i = _
  rw [← mul_assoc, ← mul_assoc, hgrp]
  show ((((Quotient.out η : stabilizer Gal(L/K) (Γ.vertexRep j)) : Gal(L/K))
      * ((h⁻¹ : stabilizer Gal(L/K) (Γ.vertexRep j)) : Gal(L/K))) * ch.τ⁻¹ * ch.σ)
      • Γ.vertexRep i = _
  rw [mul_assoc, mul_smul, mul_smul, hfix, ← mul_smul, ← mul_assoc]
  rfl

/-! ### `RQ2-2.23`'s rational structure, per summand  (G4)

`Θ σ` moves the `η`-component to `σ · η` **and** transports the fibre, so it is not a plain
reindexing: `M(cosetVertex (σ⁻¹·η))` and `M(cosetVertex η)` are different spaces.  Written as a
bare `toFun`/`invFun` pair it puts a *dependent index rewrite* in `left_inv` — after
`inv_smul_smul` the index changes, which changes the term's **type**, so the rewrite is ill-typed
rather than merely unfound.  (Not a `show`-pinning case, per `CONVENTIONS.md` §3's new entry: the
two sides genuinely live in different fibres, so no amount of shape-pinning helps.)

Factoring the action as **reindex ∘ transport** avoids it, and both halves come with mathlib's
inverse laws already proved:

* `Equiv.piCongrLeft'` reindexes along `η ↦ σ⁻¹ · η` — a pure permutation of the index;
* `Equiv.piCongrRight` applies `φ'_{·,σ}` fibrewise, with `EdgeChoice.smul_cosetVertex` supplying
  exactly the fibre identification `σ · cosetVertex (σ⁻¹·η) = cosetVertex η`.

The dependent transport is thereby confined to `smul_cosetVertex`, where it is proved once.

@census none (G4 engine for `RQ2-2.23`)
-/

/-- `Θ σ` on one edge-orbit summand: reindex by `σ⁻¹ · −`, then translate fibrewise by `φ'_{·,σ}`.
@census none (helper for `RQ2-2.23`) -/
noncomputable def rationalStructurePi (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) :
    (∀ η : EdgeChoice.CosetIndex Γ ch, M.M (EdgeChoice.cosetVertex Γ ch η)) ≃+
      (∀ η : EdgeChoice.CosetIndex Γ ch, M.M (EdgeChoice.cosetVertex Γ ch η)) where
  toEquiv :=
    (Equiv.piCongrLeft' (fun η => M.M (EdgeChoice.cosetVertex Γ ch η))
      (MulAction.toPerm σ)).trans
      (Equiv.piCongrRight fun η =>
        (M.φ' (σ : Gal(L/K)) (ch.smul_cosetVertex σ η)).toEquiv)
  map_add' f g := by
    funext η
    exact map_add (M.φ' (σ : Gal(L/K)) (ch.smul_cosetVertex σ η)) _ _

@[simp]
theorem rationalStructurePi_apply (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)))
    (f : ∀ η : EdgeChoice.CosetIndex Γ ch, M.M (EdgeChoice.cosetVertex Γ ch η))
    (η : EdgeChoice.CosetIndex Γ ch) :
    rationalStructurePi M ch σ f η
      = M.φ' (σ : Gal(L/K)) (ch.smul_cosetVertex σ η) (f (σ⁻¹ • η)) := rfl

/-- **`Θ σ`**: the semi-linear `G_{v_j}`-action on `⊕_ε ∏_η M(η τ_ε⁻¹ σ_ε v_i)`, assembled from the
per-summand action by `DirectSum.congrAddEquiv`.  @census none (helper for `RQ2-2.23`) -/
noncomputable def rationalStructureTheta (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) :
    wiiMjLRhs M ch ≃+ wiiMjLRhs M ch :=
  DirectSum.congrAddEquiv fun ε => rationalStructurePi M (ch ε) σ

@[simp]
theorem rationalStructureTheta_apply (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) (x : wiiMjLRhs M ch)
    (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)) :
    rationalStructureTheta M ch σ x ε η
      = M.φ' (σ : Gal(L/K)) ((ch ε).smul_cosetVertex σ η) (x ε (σ⁻¹ • η)) := by
  show rationalStructurePi M (ch ε) σ (x ε) η = _
  rfl

/-- **Clause `RQ2-2.23-C2`**: `Θ σ` is `σ`-semi-linear.  @census none (clause witness)
@clauses   RQ2-2.23-C2 -/
theorem rationalStructureTheta_smul (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) (a : L) (x : wiiMjLRhs M ch) :
    rationalStructureTheta M ch σ (a • x)
      = ((σ : Gal(L/K)) a) • rationalStructureTheta M ch σ x := by
  ext ε η
  rw [rationalStructureTheta_apply]
  show M.φ' _ _ ((a • x) ε (σ⁻¹ • η)) = _
  rw [show (a • x) ε (σ⁻¹ • η) = a • (x ε (σ⁻¹ • η)) from rfl, M.φ'_smul]
  rfl

/-- `Θ σ` read at any index provably equal to `σ⁻¹ · η`.

The index is a **variable** here, so `subst` applies and the dependent rewrite that branch (iii) of
`CONVENTIONS.md` §3 warns about never arises.  This is the same doctrine as `rationalStructurePi`
one level down: make the transport substitutable instead of rewriting under a dependent position.

@census none (helper) -/
theorem rationalStructureTheta_apply_of (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) (x : wiiMjLRhs M ch)
    (ε : Γ.EdgeOrbit i j) (η k : EdgeChoice.CosetIndex Γ (ch ε)) (hk : k = σ⁻¹ • η)
    (h : (σ : Gal(L/K)) • EdgeChoice.cosetVertex Γ (ch ε) k
        = EdgeChoice.cosetVertex Γ (ch ε) η) :
    rationalStructureTheta M ch σ x ε η = M.φ' (σ : Gal(L/K)) h (x ε k) := by
  subst hk
  rfl

/-- **Clause `RQ2-2.23-C3`**: the cocycle condition.  @census none (clause witness)
@clauses   RQ2-2.23-C3 -/
theorem rationalStructureTheta_comp (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (σ τ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) (x : wiiMjLRhs M ch) :
    rationalStructureTheta M ch σ (rationalStructureTheta M ch τ x)
      = rationalStructureTheta M ch (σ * τ) x := by
  ext ε η
  rw [rationalStructureTheta_apply, rationalStructureTheta_apply]
  rw [rationalStructureTheta_apply_of M ch (σ * τ) x ε η (τ⁻¹ • σ⁻¹ • η)
    (by rw [mul_inv_rev, mul_smul])
    (by
      rw [show ((σ * τ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) : Gal(L/K))
          = (σ : Gal(L/K)) * (τ : Gal(L/K)) from rfl, mul_smul]
      rw [(ch ε).smul_cosetVertex τ (σ⁻¹ • η)]
      exact (ch ε).smul_cosetVertex σ η)]
  exact M.φ'_comp (σ : Gal(L/K)) (τ : Gal(L/K)) _ _ _ _

/-- `Θ 1 = id`.  With `rationalStructureTheta_comp` this makes `Θ` a genuine `G_{v_j}`-action,
which is what lets `C6`'s continuity set be treated as a **subgroup**.  @census none (helper) -/
theorem rationalStructureTheta_one (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε) (x : wiiMjLRhs M ch) :
    rationalStructureTheta M ch 1 x = x := by
  ext ε η
  rw [rationalStructureTheta_apply_of M ch 1 x ε η η (by rw [inv_one, one_smul])
    (by rw [OneMemClass.coe_one, one_smul])]
  rw [M.φ'_congr (show ((1 : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) : Gal(L/K)) = 1 from rfl)
    _ (by rw [one_smul]), M.φ'_one]
  rfl

/-- `C6`'s continuity set, as a **subgroup**.

`Θ` is an action (`rationalStructureTheta_one`, `rationalStructureTheta_comp`), so
`{σ | Θ σ x = x}` is the stabiliser of `x` and in particular a subgroup.  That is what makes the
openness proof tractable: a subgroup is open as soon as it **contains** an open subgroup
(`Subgroup.isOpen_mono`), so one exhibits a single open subgroup inside rather than reasoning
pointwise.

Packaged as a `def` rather than a `MulAction` instance on `wiiMjLRhs M ch` deliberately: that type
already carries an `L`-module structure, and a global action instance keyed on it is exactly the
kind of competitor finding **S5-F5** was about.  The per-carrier discipline applies here too.

@census none (helper for `RQ2-2.23-C6`) -/
noncomputable def thetaStabilizer (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε) (x : wiiMjLRhs M ch) :
    Subgroup ↥(stabilizer Gal(L/K) (Γ.vertexRep j)) where
  carrier := {σ | rationalStructureTheta M ch σ x = x}
  one_mem' := rationalStructureTheta_one M ch x
  mul_mem' {a b} ha hb := by
    show rationalStructureTheta M ch (a * b) x = x
    rw [← rationalStructureTheta_comp M ch a b x]
    show rationalStructureTheta M ch a (rationalStructureTheta M ch b x) = x
    rw [show rationalStructureTheta M ch b x = x from hb]
    exact ha
  inv_mem' {a} ha := by
    show rationalStructureTheta M ch a⁻¹ x = x
    conv_lhs => rw [show x = rationalStructureTheta M ch a x from ha.symm]
    rw [rationalStructureTheta_comp M ch a⁻¹ a x, inv_mul_cancel]
    exact rationalStructureTheta_one M ch x

@[simp]
theorem mem_thetaStabilizer (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε) (x : wiiMjLRhs M ch)
    (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) :
    σ ∈ thetaStabilizer M ch x ↔ rationalStructureTheta M ch σ x = x := Iff.rfl

/-! ### `RQ2-2.23-C6`, first half: the coset index is finite

`Gal(L/K)` is **profinite** for a Galois extension (`CompactSpace Gal(K/k)`,
`FieldTheory/Galois/Profinite.lean`), `G_{v_j}` is closed in it (`isClosed_stabilizer_V`, hence
compact), and `G_{τ_ε⁻¹ e_ε}` is **open** (`RQ2-1.02-C3`).  An open subgroup of a compact group has
finite index, so the coset space is finite.

This is the second place the smoothness clause is load-bearing rather than decorative: without
`RQ2-1.02-C3` the index set of `eq:WiiMjL`'s product could be infinite and the clause's `∏ = ⊕`
identification would fail.

@census none (clause witness for `RQ2-2.23-C6`)
@clauses   RQ2-2.23-C6
-/

/-- The stabiliser of a coset is open: for `η = gH`, `σ · η = η` iff `(σg)⁻¹g ∈ H`, so the set is
the preimage of the **open** `H` under a continuous map.  @census none (helper for `RQ2-2.23-C6`) -/
theorem isOpen_index_stabilizer {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch) :
    IsOpen {σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)) | σ • η = η} := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective η
  have hopen := Subgroup.subgroupOf_isOpen (stabilizer Gal(L/K) (Γ.vertexRep j))
    (stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε)) (Γ.isOpen_stabilizer_E _)
  have hcont : Continuous
      (fun σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)) => (σ * g)⁻¹ * g) := by
    fun_prop
  have hset : {σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)) |
        σ • (QuotientGroup.mk g : EdgeChoice.CosetIndex Γ ch) = QuotientGroup.mk g}
      = (fun σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)) => (σ * g)⁻¹ * g) ⁻¹'
        (((stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε)).subgroupOf
          (stabilizer Gal(L/K) (Γ.vertexRep j)) : Subgroup _) : Set _) := by
    ext σ
    show (QuotientGroup.mk (σ * g) : EdgeChoice.CosetIndex Γ ch) = QuotientGroup.mk g ↔ _
    exact QuotientGroup.eq
  rw [hset]
  exact hopen.preimage hcont

/-- The fibre stabiliser, pulled back to `G_{v_j}`.  Open by `Rep.isOpen_fibre_stabilizer`
(`RQ2-1.08-C6`) and continuity of the inclusion.  @census none (helper for `RQ2-2.23-C6`) -/
theorem isOpen_fibre_stabilizer_sub (M : Rep Γ) (j : Γ.VertexOrbit) (w : Γ.V) (m : M.M w) :
    IsOpen {σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)) |
      ∃ h : (σ : Gal(L/K)) • w = w, M.φ' (σ : Gal(L/K)) h m = m} :=
  (M.isOpen_fibre_stabilizer w m).preimage continuous_subtype_val

/-- **Clause `RQ2-2.23-C6`, continuity.**  `{σ | Θ σ x = x}` is open.

It is a **subgroup** (`thetaStabilizer`), so `Subgroup.isOpen_of_mem_nhds` reduces the claim to
exhibiting an open set containing `1` inside it.  That set is a **finite** intersection: over `x`'s
`DFinsupp` support, and over the coset index, finite by `finite_cosetIndex`.

@census none (clause witness for `RQ2-2.23-C6`)
@clauses   RQ2-2.23-C6 -/
theorem rationalStructureTheta_isOpen (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε) (x : wiiMjLRhs M ch) :
    IsOpen {σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)) |
      rationalStructureTheta M ch σ x = x} := by
  classical
  set V : Set ↥(stabilizer Gal(L/K) (Γ.vertexRep j)) :=
    ⋂ ε ∈ (DFinsupp.support x : Finset (Γ.EdgeOrbit i j)),
      ⋂ η : EdgeChoice.CosetIndex Γ (ch ε),
        ({σ | σ • η = η} ∩
          {σ | ∃ h : (σ : Gal(L/K)) • EdgeChoice.cosetVertex Γ (ch ε) η
              = EdgeChoice.cosetVertex Γ (ch ε) η,
            M.φ' (σ : Gal(L/K)) h (x ε η) = x ε η}) with hV
  have hVopen : IsOpen V := by
    refine Set.Finite.isOpen_biInter (DFinsupp.support x).finite_toSet fun ε _ => ?_
    haveI := finite_cosetIndex (ch ε)
    refine isOpen_iInter_of_finite fun η => ?_
    exact (isOpen_index_stabilizer (ch ε) η).inter
      (isOpen_fibre_stabilizer_sub M j _ (x ε η))
  have hV1 : (1 : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) ∈ V := by
    simp only [hV, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    refine fun ε _ η => ⟨one_smul _ _, ?_, ?_⟩
    · show ((1 : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) : Gal(L/K)) • _ = _
      rw [show ((1 : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) : Gal(L/K)) = 1 from rfl, one_smul]
    · rw [M.φ'_congr (show ((1 : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) : Gal(L/K)) = 1 from rfl)
        _ (by rw [one_smul]), M.φ'_one]
      rfl
  have hVsub : V ⊆ (thetaStabilizer M ch x : Set _) := by
    intro σ hσ
    simp only [hV, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq] at hσ
    show rationalStructureTheta M ch σ x = x
    ext ε η
    by_cases hε : ε ∈ DFinsupp.support x
    · obtain ⟨hidx, hfib⟩ := hσ ε hε η
      rw [rationalStructureTheta_apply_of M ch σ x ε η η
        (show η = σ⁻¹ • η by rw [eq_inv_smul_iff, hidx]) hfib.choose]
      exact hfib.choose_spec
    · have hx0 : x ε = 0 := DFinsupp.notMem_support_iff.mp hε
      rw [rationalStructureTheta_apply]
      simp [hx0]
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hVopen.mem_nhds hV1) hVsub)






/-! ### `RQ2-2.23` clause `C5` — the canonical rational structure, and the source's computation

`C5` says the `Θ` of `C1` **is** the rational structure that `W_i ⊗_{L_i} {}_iM_j ⊆ W_i ⊗_{L_i}
{}_iM_j ⊗_{L_j} L` already carries: for any identification `e` of the two sides of `eq:WiiMjL`,
`Θ(σ) ∘ e = e ∘ c(σ)`, where `c(σ)` is "apply `σ` to the `L` factor".

Unwound on the generator `(w ⊗ m) ⊗ a`, both sides are a scalar times a translate of `w`, and the
whole content is that **two bookkeeping discrepancies cancel**.  Writing `k := σ⁻¹·η`, the source's
`eq:explicitdecompositiontwisting`, `η τ_ε⁻¹` is only defined up to the coset, so `σ · rep(k)` and
`rep(η)` differ by some `g ∈ G_{τ_ε⁻¹ e_ε}` (`EdgeChoice.rep_smul_eq`).  That `g` then has to
disappear twice, and does so for two *different* reasons:

* on the **scalar** `(rep k · τ_ε⁻¹)(m_ε)`, because `g` fixes `τ_ε⁻¹(L(e_ε)) = L(τ_ε⁻¹e_ε)`
  pointwise (`fix_of_mem_stabilizer_tau`, clause `RQ2-1.02-C3`);
* on the **vector** `φ_{rep k τ_ε⁻¹σ_ε}(w)`, because `g` fixes the *vertex*
  `τ_ε⁻¹σ_ε v_i = s(τ_ε⁻¹e_ε)` (S4's `stabilizer_le_source`) and `w ∈ W_i = M(v_i)^{G_{v_i}}`
  (`Rep.φ'_insert_of_vertexFixed`).

The second is where `W_i` being the **invariants** is load-bearing rather than decorative: for a
general `m ∈ M(v_i)` the identity is false, and `C5` with it.  That is the same clause-`RQ2-2.20-H1`
fact the row's own hypothesis names, showing up as an arithmetic obligation.

@census none (G4 engine for `RQ2-2.23-C5`)
-/

/-- **The coset discrepancy, isolated.**  `σ · rep(σ⁻¹·η)` and `rep(η)` are two representatives of
one coset, so they differ by an element of `G_{τ_ε⁻¹ e_ε}`.

This is the group fact `EdgeChoice.smul_cosetVertex` uses inline; `C5` needs it twice more, against
two different things it acts on, so it is named here.

@census none (helper for `RQ2-2.23-C5`) -/
theorem EdgeChoice.rep_smul_eq {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (σ : stabilizer Gal(L/K) (Γ.vertexRep j))
    (η : EdgeChoice.CosetIndex Γ ch) :
    ∃ g : Gal(L/K), g ∈ stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε) ∧
      (σ : Gal(L/K)) * EdgeChoice.rep Γ ch (σ⁻¹ • η)
        = EdgeChoice.rep Γ ch η * g := by
  have hmem : (Quotient.out (σ⁻¹ • η))⁻¹ * (σ⁻¹ * Quotient.out η)
      ∈ (stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε)).subgroupOf
          (stabilizer Gal(L/K) (Γ.vertexRep j)) := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' η]
    rfl
  set h : stabilizer Gal(L/K) (Γ.vertexRep j) :=
    (Quotient.out (σ⁻¹ • η))⁻¹ * (σ⁻¹ * Quotient.out η) with hh
  refine ⟨((h⁻¹ : stabilizer Gal(L/K) (Γ.vertexRep j)) : Gal(L/K)),
    (Subgroup.mem_subgroupOf).mp (inv_mem hmem), ?_⟩
  have h2 : (Quotient.out (σ⁻¹ • η)) * h = σ⁻¹ * Quotient.out η := by rw [hh]; group
  have h3 : σ * (Quotient.out (σ⁻¹ • η) * h) = Quotient.out η := by
    rw [h2, ← mul_assoc, mul_inv_cancel, one_mul]
  have h4 : σ * Quotient.out (σ⁻¹ • η) = Quotient.out η * h⁻¹ := by
    rw [← h3, mul_assoc, mul_inv_cancel_right]
  exact congrArg (fun t : stabilizer Gal(L/K) (Γ.vertexRep j) => (t : Gal(L/K))) h4

/-- `W_v`'s invariance, in the form the composition law consumes: an element `g` fixing `u · v` may
be inserted between `u` and nothing at all when it acts on `W_v`.

@census none (helper for `RQ2-2.23-C5`) -/
theorem Rep.φ'_insert_of_vertexFixed_aux (M : Rep Γ) {v z : Γ.V}
    (w : ↥(M.vertexFixed v)) (u g : Gal(L/K)) (hg : g • (u • v) = u • v)
    (h : (g * u) • v = z) (h' : u • v = z) :
    M.φ' (g * u) h (w : M.M v) = M.φ' u h' (w : M.M v) := by
  have hgi : (u⁻¹ * g * u) • v = v := by
    rw [mul_smul, mul_smul, hg, ← mul_smul, inv_mul_cancel, one_smul]
  have hfix : M.φ' ((u⁻¹ * g * u : Gal(L/K))) hgi (w : M.M v) = (w : M.M v) :=
    w.2 ⟨u⁻¹ * g * u, hgi⟩
  have h3 : (u * (u⁻¹ * g * u)) • v = z := by
    rw [show u * (u⁻¹ * g * u) = g * u by group]; exact h
  have hc := M.φ'_comp u (u⁻¹ * g * u) hgi h' h3 (w : M.M v)
  rw [hfix] at hc
  rw [M.φ'_congr (show (g * u) = u * (u⁻¹ * g * u) by group) h h3, ← hc]

/-- The same with a prefix: `φ'_{r g u}(w) = φ'_{r u}(w)` on `W_v`, whenever `g` fixes `u · v`.
This is the shape `RQ2-2.23-C5` meets, with `r = rep η`, `u = τ_ε⁻¹σ_ε` and `g` the coset
discrepancy.  @census none (helper for `RQ2-2.23-C5`) -/
theorem Rep.φ'_insert_of_vertexFixed (M : Rep Γ) {v z : Γ.V}
    (w : ↥(M.vertexFixed v)) (r u g : Gal(L/K)) (hg : g • (u • v) = u • v)
    (h : (r * (g * u)) • v = z) (h' : (r * u) • v = z) :
    M.φ' (r * (g * u)) h (w : M.M v) = M.φ' (r * u) h' (w : M.M v) := by
  have hgu : (g * u) • v = u • v := by rw [mul_smul, hg]
  have hkey : M.φ' (g * u) hgu (w : M.M v) = M.φ' u rfl (w : M.M v) :=
    M.φ'_insert_of_vertexFixed_aux w u g hg hgu rfl
  have h₂ : r • (u • v) = z := by rw [← mul_smul]; exact h'
  have c1 := M.φ'_comp r (g * u) hgu h₂ h (w : M.M v)
  have c2 := M.φ'_comp r u rfl h₂ h' (w : M.M v)
  rw [← c1, ← c2, hkey]

/-- **The arithmetic core of clause `RQ2-2.23-C5`.**  On the `(ε,η)`-component of a generator, `Θ(σ)`
applied to the `σ⁻¹·η`-entry gives the `η`-entry with `a` replaced by `σ(a)`.

Both bookkeeping discrepancies of the section header are discharged here, and they are the whole
proof: `φ'_smul` moves `σ` onto the scalar, `fix_of_mem_stabilizer_tau` removes the coset
discrepancy from it, and `φ'_insert_of_vertexFixed` removes the same discrepancy from the vector
using `w ∈ W_i`.

@census none (clause witness for `RQ2-2.23-C5`)
@clauses   RQ2-2.23-C5 -/
theorem Rep.theta_core (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (σ : stabilizer Gal(L/K) (Γ.vertexRep j))
    (η : EdgeChoice.CosetIndex Γ ch) (a : L) (c : ↥(Γ.edgeOrbitField ε))
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) :
    M.φ' (σ : Gal(L/K)) (ch.smul_cosetVertex σ η)
        ((a * (EdgeChoice.rep Γ ch (σ⁻¹ • η) * ch.τ⁻¹) (c : L))
          • M.φ (EdgeChoice.rep Γ ch (σ⁻¹ • η) * ch.τ⁻¹ * ch.σ) (Γ.vertexRep i)
              (w : M.M (Γ.vertexRep i)))
      = ((σ : Gal(L/K)) a * (EdgeChoice.rep Γ ch η * ch.τ⁻¹) (c : L))
          • M.φ (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ) (Γ.vertexRep i)
              (w : M.M (Γ.vertexRep i)) := by
  obtain ⟨g, hg, hgeq⟩ := ch.rep_smul_eq σ η
  rw [M.φ'_smul]
  have hscal : (σ : Gal(L/K)) (a * (EdgeChoice.rep Γ ch (σ⁻¹ • η) * ch.τ⁻¹) (c : L))
      = (σ : Gal(L/K)) a * (EdgeChoice.rep Γ ch η * ch.τ⁻¹) (c : L) := by
    rw [map_mul]
    congr 1
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply,
      show (σ : Gal(L/K)) ((EdgeChoice.rep Γ ch (σ⁻¹ • η)) (ch.τ⁻¹ (c : L)))
        = ((σ : Gal(L/K)) * EdgeChoice.rep Γ ch (σ⁻¹ • η)) (ch.τ⁻¹ (c : L)) from
        (AlgEquiv.mul_apply _ _ _).symm, hgeq, AlgEquiv.mul_apply,
      fix_of_mem_stabilizer_tau ch hg c]
  have hsrc : (ch.τ⁻¹ * ch.σ) • Γ.vertexRep i
      = Γ.toRQuiver.source (ch.τ⁻¹ • Γ.edgeRep ε) := by
    rw [mul_smul, ch.source_eq, Γ.source_smul]
  have hgfix : g • ((ch.τ⁻¹ * ch.σ) • Γ.vertexRep i) = (ch.τ⁻¹ * ch.σ) • Γ.vertexRep i := by
    rw [hsrc]; exact Γ.stabilizer_le_source _ hg
  have hgeq' : (σ : Gal(L/K)) * (EdgeChoice.rep Γ ch (σ⁻¹ • η) * ch.τ⁻¹ * ch.σ)
      = EdgeChoice.rep Γ ch η * (g * (ch.τ⁻¹ * ch.σ)) := by
    rw [show (σ : Gal(L/K)) * (EdgeChoice.rep Γ ch (σ⁻¹ • η) * ch.τ⁻¹ * ch.σ)
        = ((σ : Gal(L/K)) * EdgeChoice.rep Γ ch (σ⁻¹ • η)) * (ch.τ⁻¹ * ch.σ) by group, hgeq]
    group
  have h₃ : ((σ : Gal(L/K)) * (EdgeChoice.rep Γ ch (σ⁻¹ • η) * ch.τ⁻¹ * ch.σ))
      • Γ.vertexRep i = EdgeChoice.cosetVertex Γ ch η := by
    rw [mul_smul]; exact ch.smul_cosetVertex σ η
  have h₄ : (EdgeChoice.rep Γ ch η * (g * (ch.τ⁻¹ * ch.σ))) • Γ.vertexRep i
      = EdgeChoice.cosetVertex Γ ch η := by rw [← hgeq']; exact h₃
  have h₅ : (EdgeChoice.rep Γ ch η * (ch.τ⁻¹ * ch.σ)) • Γ.vertexRep i
      = EdgeChoice.cosetVertex Γ ch η := by
    show _ = (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ) • Γ.vertexRep i
    rw [mul_assoc]
  have step1 := M.φ'_comp (σ : Gal(L/K)) (EdgeChoice.rep Γ ch (σ⁻¹ • η) * ch.τ⁻¹ * ch.σ)
      rfl (ch.smul_cosetVertex σ η) h₃ (w : M.M (Γ.vertexRep i))
  have step2 := M.φ'_insert_of_vertexFixed w (EdgeChoice.rep Γ ch η) (ch.τ⁻¹ * ch.σ) g
      hgfix h₄ h₅
  have hvec : M.φ' (σ : Gal(L/K)) (ch.smul_cosetVertex σ η)
        (M.φ (EdgeChoice.rep Γ ch (σ⁻¹ • η) * ch.τ⁻¹ * ch.σ) (Γ.vertexRep i)
          (w : M.M (Γ.vertexRep i)))
      = M.φ (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ) (Γ.vertexRep i)
          (w : M.M (Γ.vertexRep i)) := by
    rw [show M.φ (EdgeChoice.rep Γ ch (σ⁻¹ • η) * ch.τ⁻¹ * ch.σ) (Γ.vertexRep i)
          (w : M.M (Γ.vertexRep i))
        = M.φ' (EdgeChoice.rep Γ ch (σ⁻¹ • η) * ch.τ⁻¹ * ch.σ) rfl
          (w : M.M (Γ.vertexRep i)) from rfl, step1,
      M.φ'_congr hgeq' h₃ h₄, step2,
      M.φ'_congr (show EdgeChoice.rep Γ ch η * (ch.τ⁻¹ * ch.σ)
          = EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ from (mul_assoc _ _ _).symm) h₅
        (rfl : (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ) • Γ.vertexRep i
          = EdgeChoice.cosetVertex Γ ch η)]
    rfl
  rw [hscal, hvec]

/-- **Induction over `wiiMjL`'s double generators.**  `W_i ⊗_{L_i} {}_iM_j ⊗_{L_j} L` is a quotient
of a tensor square, so a property additive in `x` and true of `(w ⊗ m) ⊗ a` is true everywhere.

Both levels are `Balanced` quotients, so the argument is `Submodule.Quotient.mk_surjective` and
`TensorProduct.induction_on`, twice; `Balanced.mk_zero_left`/`Balanced.mk_add_left` carry the outer
constructor through the inner induction.  This is the spanning statement that makes the pin of
`RQ2-2.20-C1` determine its map, used here as an induction principle.

@census none (helper for `RQ2-2.23-C5`) -/
theorem wiiMjL_induction (M : Rep Γ) {i j : Γ.VertexOrbit}
    {P : wiiMjL M i j → Prop}
    (h0 : P 0)
    (hmk : ∀ (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) (a : L),
      P (Balanced.mk (Balanced.mk w m) a))
    (hadd : ∀ x y, P x → P y → P (x + y)) (x : wiiMjL M i j) : P x := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective
    (balancedRel K (Γ.toSpecies.L j) L L
      (EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i)))) x
  induction s with
  | zero => simpa using h0
  | tmul a t =>
      show P (Balanced.mk t a)
      obtain ⟨s', rfl⟩ := Submodule.Quotient.mk_surjective
        (balancedRel K (Γ.toSpecies.L i) (Γ.toSpecies.L j) (Γ.toSpecies.M i j)
          ↥(M.vertexFixed (Γ.vertexRep i))) t
      induction s' with
      | zero =>
          have hz : (Submodule.Quotient.mk (p := balancedRel K (Γ.toSpecies.L i)
              (Γ.toSpecies.L j) (Γ.toSpecies.M i j) ↥(M.vertexFixed (Γ.vertexRep i)))
              (0 : Γ.toSpecies.M i j ⊗[K] ↥(M.vertexFixed (Γ.vertexRep i))))
              = (0 : EtaleSpecies.Rep.tensor Γ.toSpecies i j
                  ↥(M.vertexFixed (Γ.vertexRep i))) := rfl
          rw [hz, Balanced.mk_zero_left]
          exact h0
      | tmul m w => exact hmk w m a
      | add p q hp hq =>
          have hp2 : (Submodule.Quotient.mk (p := balancedRel K (Γ.toSpecies.L i)
              (Γ.toSpecies.L j) (Γ.toSpecies.M i j) ↥(M.vertexFixed (Γ.vertexRep i))) (p + q))
              = Submodule.Quotient.mk p + Submodule.Quotient.mk q := rfl
          rw [hp2, Balanced.mk_add_left]
          exact hadd _ _ hp hq
  | add s t hs ht =>
      have hmk2 : Submodule.Quotient.mk (p := balancedRel K (Γ.toSpecies.L j) L L
          (EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i)))) (s + t)
          = Submodule.Quotient.mk s + Submodule.Quotient.mk t := rfl
      rw [hmk2]; exact hadd _ _ hs ht

/-- **`RQ2-2.20-C1`'s pin determines its isomorphism** — canonicity, as a theorem rather than as a
docstring remark.

`§54.2` observed that the generators `Balanced.mk (Balanced.mk w m) a` span, so the pin determines
`e`; this is that observation compiled, using `wiiMjL_induction` above.  It is what the word
**canonical** in `eq:WiiMjLpre` means, and it is the reason the upgraded `C1` is a genuine pinning
rather than a decorated `Nonempty`.

**It is also the soundness argument for finding `S5-F8`'s repair (b)** (§56.4): the scaled
identification `c · e₀`, which satisfies `IsEdgeDescent` for `c ∈ L(v_j)ˣ` and is what makes the
four `∀ e₀ f` clauses collapse, **cannot satisfy this pin** unless it equals `e₀` — so pinning
`e₀` inside `IsEdgeDescent` closes the collision at its source.

@census none (helper; canonicity of `RQ2-2.20-C1`, soundness input for `S5-F8`) -/
theorem wiiMjPre_pin_unique (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₁ e₂ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (h₁ : ∀ (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) (a : L)
        (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)),
      e₁ (Balanced.mk (Balanced.mk w m) a) ε η
        = Twist.ofL (a * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹) ((m ε : L)))
            ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
                (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)] w)
    (h₂ : ∀ (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) (a : L)
        (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)),
      e₂ (Balanced.mk (Balanced.mk w m) a) ε η
        = Twist.ofL (a * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹) ((m ε : L)))
            ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
                (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)] w)
    (x : wiiMjL M i j) : e₁ x = e₂ x := by
  induction x using wiiMjL_induction with
  | h0 => rw [e₁.map_zero, e₂.map_zero]
  | hmk w m a => ext ε η; rw [h₁, h₂]
  | hadd p q hp hq => rw [e₁.map_add, e₂.map_add, hp, hq]


/-- **Clause `RQ2-2.23-C5`.**  `Θ` agrees with the canonical rational structure: for the `RQ2-2.22`
identification `e` and any `c(σ)` acting as `σ` on the `L` factor, `Θ(σ) ∘ e = e ∘ c(σ)`.

`e` is `RQ2-2.22`'s composite at `RQ2-2.20`'s identification, so both sides are *computed*, not
merely compared: `wiiMjL_induction` reduces to the generator `(w ⊗ m) ⊗ a`, `RQ2-2.20`'s pin
(`V-S5b-6`, discharged) evaluates `e₀` there, `RQ2-2.22`'s pin evaluates `ψ`, and `Rep.theta_core`
is the resulting identity.

**This is the first place `RQ2-2.20-C1`'s pin is *consumed*.**  With `C1` still a bare `Nonempty`
the reduction stops at "there is some `e₀`" and the generator case cannot be evaluated at all —
which is exactly the propagation the S5b verifier predicted (`V-S5b-6`, §D.6) and the reason §31
coupled the pin to this row's neighbourhood rather than deferring it.

@census none (clause witness for `RQ2-2.23-C5`)
@clauses   RQ2-2.23-C5 -/
theorem rationalStructure_agrees (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε) :
    ∃ e : wiiMjL M i j ≃ₗ[L] wiiMjLRhs M ch,
      ∀ (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)))
        (c : wiiMjL M i j ≃+ wiiMjL M i j),
      (∀ (t : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i)))
          (a : L), c (Balanced.mk t a) = Balanced.mk t ((σ : Gal(L/K)) a)) →
      ∀ x : wiiMjL M i j,
        rationalStructureTheta M ch σ (e x) = e (c x) := by
  obtain ⟨e₀, h₀⟩ := wiiMj_baseChange_pre M i j ch
  obtain ⟨ψ, hψ, hcomp⟩ := wiiMj_baseChange M i j ch
  obtain ⟨e, he⟩ := hcomp e₀
  refine ⟨e, ?_⟩
  intro σ c hc x
  induction x using wiiMjL_induction with
  | h0 =>
      have l1 : e (0 : wiiMjL M i j) = 0 := e.map_zero
      have l2 : c (0 : wiiMjL M i j) = 0 := c.map_zero
      have l3 : rationalStructureTheta M ch σ (0 : wiiMjLRhs M ch) = 0 :=
        (rationalStructureTheta M ch σ).map_zero
      exact (congrArg (rationalStructureTheta M ch σ) l1).trans
        (l3.trans (l1.symm.trans (congrArg (fun z => e z) l2.symm)))
  | hmk w m a =>
      rw [hc]
      ext ε η
      have hL := h₀ w m a ε (σ⁻¹ • η)
      have hR := h₀ w m ((σ : Gal(L/K)) a) ε η
      rw [rationalStructureTheta_apply, he, he]
      have e1 : (ψ ε (σ⁻¹ • η)) ((e₀ (Balanced.mk (Balanced.mk w m) a)) ε (σ⁻¹ • η))
          = (a * (EdgeChoice.rep Γ (ch ε) (σ⁻¹ • η) * (ch ε).τ⁻¹) ((m ε : L)))
              • M.φ (EdgeChoice.rep Γ (ch ε) (σ⁻¹ • η) * (ch ε).τ⁻¹ * (ch ε).σ)
                  (Γ.vertexRep i) (w : M.M (Γ.vertexRep i)) :=
        (congrArg (ψ ε (σ⁻¹ • η)) hL).trans (hψ ε (σ⁻¹ • η) _ w)
      have e2 : (ψ ε η) ((e₀ (Balanced.mk (Balanced.mk w m) ((σ : Gal(L/K)) a))) ε η)
          = ((σ : Gal(L/K)) a * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹) ((m ε : L)))
              • M.φ (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)
                  (Γ.vertexRep i) (w : M.M (Γ.vertexRep i)) :=
        (congrArg (ψ ε η) hR).trans (hψ ε η _ w)
      rw [e1, e2]
      exact M.theta_core (ch ε) σ η a (m ε) w
  | hadd p q hp hq =>
      have l1 : e (p + q) = e p + e q := e.map_add p q
      have l2 : c (p + q) = c p + c q := c.map_add p q
      have l3 : e (c p + c q) = e (c p) + e (c q) := e.map_add _ _
      have l4 : rationalStructureTheta M ch σ (e p + e q)
          = rationalStructureTheta M ch σ (e p) + rationalStructureTheta M ch σ (e q) :=
        (rationalStructureTheta M ch σ).map_add _ _
      exact (congrArg (rationalStructureTheta M ch σ) l1).trans
        (l4.trans ((congrArg₂ (· + ·) hp hq).trans
          (l3.symm.trans (congrArg (fun z => e z) l2.symm))))

/-- **Proposition `prop:rationalstructures`** (census `RQ2-2.23`).

Through the identification `eq:WiiMjL` of `RQ2-2.22` (clause `RQ2-2.23-H1`), and for every
`σ ∈ Gal(L/L(v_j)) = G_{v_j}` (clause `RQ2-2.23-H2`), the maps

`Θ_{ij}(σ) : (m_{ε,η}) ↦ (φ_{σ^{-1}η τ_ε^{-1}σ_ε v_i, σ}(m_{ε,σ^{-1}η}))`  (clause `C1`)

are `σ`-**linear** (`C2`), satisfy the **cocycle** condition `Θ(σ)∘Θ(τ) = Θ(στ)` (`C3`), act
**continuously** (`C6`), and therefore constitute an `L(v_j)`-**rational structure** (`C4`) — which
**agrees** with the canonical one given by the inclusion
`W_i ⊗_{L_i} {}_iM_j ⊆ W_i ⊗_{L_i} {}_iM_j ⊗_{L_j} L` (`C5`, the proposition's own statement).

@census    RQ2-2.23
@source    prop:rationalstructures
@clauses   RQ2-2.23-H1, RQ2-2.23-H2, RQ2-2.23-C1, RQ2-2.23-C2, RQ2-2.23-C3, RQ2-2.23-C4, RQ2-2.23-C5,
           RQ2-2.23-C6
@imports   none
@divergence JUSTIFIED_REFORMULATION on clauses `RQ2-2.23-C4` and `RQ2-2.23-C5`.

`C4` — "`Θ_{ij}` **is** an `L(v_j)`-rational structure" is delivered as the conjunction of exactly
the three conditions `RQ2-1.16` requires of one: `σ`-linearity (`C2`), the cocycle law (`C3`) and
continuity (`C6`).  It is *not* stated as `Descent.KStructure ↥(L(v_j)) L —`, because S0's class is
indexed by `Gal(L/L(v_j))` while the group acting here is `G_{v_j} = stabilizer Gal(L/K) v_j`; the
two are isomorphic by the Galois correspondence (`L(v_j)` being *defined* as `L^{G_{v_j}}`) but not
equal, and transporting along that isomorphism inside the statement would put a `cast` in a
census-carrying signature — the shape stage S2 named as the archetypal `WEAKENED_OR_PARTIAL` risk
and avoided the same way.  Nothing is lost: the three conjuncts *are* the definition, and the G4
bridge to `KStructure` is a helper, not a statement.

`C5` — the canonical structure is characterised rather than constructed: the statement quantifies
over any additive automorphism `c σ` of `W_i ⊗_{L_i} {}_iM_j ⊗_{L_j} L` acting on pure tensors by
`w ⊗ m ⊗ a ↦ w ⊗ m ⊗ σ a` — which is the source's own description of it — and asserts
`Θ(σ) ∘ e = e ∘ c σ` for a **named, existentially supplied** identification
`e : wiiMjL M i j ≃ₗ[L] wiiMjLRhs M ch` of `RQ2-2.22`'s shape.  Since pure tensors span, `c σ` is
determined by that formula, so this says exactly "the two rational structures agree", relative to
`RQ2-2.22`'s isomorphism in the same way `RQ2-2.22-C2` is relative to `RQ2-2.20`'s.

> **Dated correction, 2026-09-02 (`WORKFLOW.md` §7 class 7 / R6; G4 finding `V-S5G4-2`).** This
> paragraph read "`Θ(σ) ∘ e = e ∘ c σ` **for every** `RQ2-2.22` identification `e`".  The conjunct
> is and has been `∃ e : wiiMjL M i j ≃ₗ[L] wiiMjLRhs M ch, …` since the `V-S5b-1` quantifier
> repair (sanctioned and verified at G2, `VERIFICATION-S5b.md` §D.3/§F.1); the universal quantifier
> that remains is the one over `c σ`, which is what pins the canonical structure.  The disclosure
> was not swept with the repair.  Corrected in place; no statement, proof or clause changes.  The
> `∃`-form is the weaker reading of the two, so the cell was over-claiming, not hiding a weakening.

**Clause `C6` is stated as its own conjunct, not folded into `C4`.**  It was added post-freeze
(census r4, closing `AN-27`): under the *corrected* `RQ2-1.16` a rational structure must be
continuous, and the source's §2.6 had concluded "hence we obtain an `L(v_j)`-rational structure"
without checking it — a step the D2 edit turned from vacuous into real, and which `RQ2-2.24` then
invokes Galois descent for.  The two ingredients the clause names are stated with it: the index set
`G_{v_j}/G_{τ_ε^{-1}e_ε}` is **finite**, `G_{τ_ε^{-1}e_ε}` being open in `G_{v_j}`; and continuity
itself in the open-stabilizer form `census/NOTATION.md` §12 prescribes and stage S2 used for
`RQ2-1.08-C6`.

Proof plan (G4): `C1`'s shuffle is `EdgeChoice.smul_cosetVertex`; `C2`/`C3` are componentwise from
`Rep.φ'_smul` and `Rep.φ'_comp`; `C6`'s finiteness is the openness of an edge stabilizer inside a
vertex stabilizer (`RationalQuiver.smooth_E` plus compactness of `Gal(L/K)`), and its
open-stabilizer half is `Rep.smooth` transported through the finitely many components; `C5` is the
source's computation via `eq:explicitdecompositiontwisting` and the commuting square
`eq:semi-linearsquare` of `RQ2-2.21-C5`.
-/
theorem rationalStructure_eq (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε) :
    ∃ Θ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)) →
        (wiiMjLRhs M ch ≃+ wiiMjLRhs M ch),
      -- `C1`: the defining formula
      (∀ (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) (x : wiiMjLRhs M ch)
          (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)),
        (Θ σ x) ε η
          = M.φ' (σ : Gal(L/K)) ((ch ε).smul_cosetVertex σ η) (x ε (σ⁻¹ • η))) ∧
      -- `C2`: `σ`-linearity
      (∀ (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) (a : L) (x : wiiMjLRhs M ch),
        Θ σ (a • x) = (σ : Gal(L/K)) a • Θ σ x) ∧
      -- `C3`: the cocycle condition
      (∀ (σ τ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) (x : wiiMjLRhs M ch),
        Θ σ (Θ τ x) = Θ (σ * τ) x) ∧
      -- `C6`: the index set is finite, and the action is continuous
      ((∀ ε : Γ.EdgeOrbit i j, Finite (EdgeChoice.CosetIndex Γ (ch ε))) ∧
        ∀ x : wiiMjLRhs M ch,
          IsOpen {σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)) | Θ σ x = x}) ∧
      -- `C5`: agreement with the canonical rational structure
      (∃ e : wiiMjL M i j ≃ₗ[L] wiiMjLRhs M ch,
        ∀ (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)))
          (c : wiiMjL M i j ≃+ wiiMjL M i j),
        (∀ (t : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i)))
            (a : L), c (Balanced.mk t a) = Balanced.mk t ((σ : Gal(L/K)) a)) →
        ∀ x : wiiMjL M i j, Θ σ (e x) = e (c x)) :=
  ⟨rationalStructureTheta M ch, rationalStructureTheta_apply M ch,
    rationalStructureTheta_smul M ch, rationalStructureTheta_comp M ch,
    ⟨fun ε => finite_cosetIndex (ch ε), rationalStructureTheta_isOpen M ch⟩,
    rationalStructure_agrees M ch⟩

/-! ### `RQ2-2.24` — `Φ_{ij}` descends -/

/-- `η τ_ε^{-1} · t(e_ε) = v_j`: the reason the composite defining `Φ_{ij}` lands in `M(v_j)`.
`τ_ε^{-1}` pulls `t(e_ε)` back to `v_j` (`EdgeChoice.inv_smul_target`) and `η ∈ G_{v_j}` fixes it.

@census none (clause witness for `RQ2-2.24-H1`)
@clauses   RQ2-2.24-H1
-/
theorem EdgeChoice.cosetTarget {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch) :
    (EdgeChoice.rep Γ ch η * ch.τ⁻¹) • Γ.toRQuiver.target (Γ.edgeRep ε) = Γ.vertexRep j := by
  -- `τ_ε⁻¹` sends `t(e_ε)` back to `v_j` (`ch.target_eq`), and `rep η` stabilises `v_j`.
  rw [← ch.target_eq, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
  exact (Quotient.out η : stabilizer Gal(L/K) (Γ.vertexRep j)).2

/-- `σ_ε · v_i = s(e_ε)`, in the direction `Φ_{ij}` uses it.  @census none (helper) -/
theorem EdgeChoice.sourceVertex {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) :
    ch.σ • Γ.vertexRep i = Γ.toRQuiver.source (Γ.edgeRep ε) := ch.source_eq

/-- The `(ε,η)`-component of `Φ_{ij}`: `φ_{t(e_ε), η τ_ε^{-1}} ∘ φ_{e_ε} ∘ φ_{v_i, σ_ε}`, exactly
the composite the source displays (with `φ_{v_i,σ_ε}` — the census records that the source prints
`φ_{e_i,σ_ε}`, clause `RQ2-2.24-H1`'s note).

@census none (clause witness for `RQ2-2.24-H1`)
@clauses   RQ2-2.24-H1
-/
noncomputable def phiComp (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch)
    (m : ↥(M.vertexFixed (Γ.vertexRep i))) : M.M (Γ.vertexRep j) :=
  M.φ' (EdgeChoice.rep Γ ch η * ch.τ⁻¹) (ch.cosetTarget η)
    (M.φEdge' (Γ.edgeRep ε) rfl rfl
      (M.φ' ch.σ ch.sourceVertex (m : M.M (Γ.vertexRep i))))


/-! ### `RQ2-2.24`'s engine — `Φ_{ij}`, and the two halves of its equivariance  (G4)

`Φ_{ij}` is built where the source builds it: componentwise on `eq:WiiMjLpre`'s right-hand side,
`ofL a ⊗ m ↦ a · φ_{t(e_ε),ητ_ε⁻¹} φ_{e_ε} φ_{v_i,σ_ε}(m)`.  Three things have to be established
before that is even a definition, and all three are the same fact wearing different clothes — the
coset representative `rep η` is only determined up to `G_{τ_ε⁻¹e_ε}`, so **everything the formula
does must be insensitive to that ambiguity**:

* the **balance** over `TwistBase (L(v_i)) (ητ_ε⁻¹σ_ε)` — `phiComp` is `ητ_ε⁻¹σ_ε`-semilinear
  (`phiComp_smul_base`), which is what makes `phiTensorAdd`'s `liftAddHom` well defined and is the
  formal content of the source's twist;
* the **vector** half of equivariance — `φ'_σ` carries the `η`-component to the `σ·η`-component
  (`phiComp_smul_index`), which is where the ambiguity is discharged, via `phiPre_fixed`;
* the **scalar** half — `σ` carries the twist `ητ_ε⁻¹` to `(σ·η)τ_ε⁻¹` on `L(e_ε)`
  (`EdgeChoice.smul_twist_apply`), the same discharge on the other factor.

`phiPre` is the device that makes the second one provable: `phiComp` factors as
"translate by `τ_ε⁻¹`, then by `rep η`" (`phiComp_eq_phiPre`), and the **first** factor is
`G_{τ_ε⁻¹e_ε}`-fixed (`phiPre_fixed`) — because `g` there fixes the *edge* `τ_ε⁻¹e_ε`, hence its
source, and `w ∈ W_i = M(v_i)^{G_{v_i}}` absorbs the rest.  That is `RQ2-2.23-C5`'s cancellation
(§55.2) a second time, now with the edge-equivariance clause `RQ2-1.08-C9` doing the transport
(`Rep.φEdge'_φ'`) instead of a bare `φ'`.

**`Φ` is unique.**  `preRhs_addHom_ext` says two additive maps agreeing on the
`(ε,η)`-generators agree, so clause `RQ2-2.24-H1` **determines** `Φ` — which is what makes
`IsEdgeDescent`'s `∀ Φ` a quantifier over a single map rather than a strengthening.

**Placement is instance-parameterised, per §49**: `Fintype`/`DecidableEq` on the two index sets
arrive as binders, so this section commits nothing about where it sits.

@census none (G4 engine for `RQ2-2.24`)
-/
/-- `τ_ε⁻¹ σ_ε v_i = s(τ_ε⁻¹ e_ε)`.  -/
theorem EdgeChoice.tauSource {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) :
    (ch.τ⁻¹ * ch.σ) • Γ.vertexRep i = Γ.toRQuiver.source (ch.τ⁻¹ • Γ.edgeRep ε) := by
  rw [mul_smul, ch.source_eq, Γ.source_smul]

/-- `τ_ε⁻¹ t(e_ε) = v_j`. -/
theorem EdgeChoice.tauTarget {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) :
    ch.τ⁻¹ • Γ.toRQuiver.target (Γ.edgeRep ε) = Γ.vertexRep j := by
  rw [← Γ.target_smul]; exact target_tau_inv_edgeRep ch

/-- The `τ_ε⁻¹`-translate of `Φ`'s edge composite, in `M(v_j)`. -/
noncomputable def phiPre (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (m : ↥(M.vertexFixed (Γ.vertexRep i))) : M.M (Γ.vertexRep j) :=
  M.φ' ch.τ⁻¹ ch.tauTarget
    (M.φEdge' (Γ.edgeRep ε) rfl rfl
      (M.φ' ch.σ ch.sourceVertex (m : M.M (Γ.vertexRep i))))

/-- `phiPre` is the transported edge map applied to the transported `m`. -/
theorem phiPre_eq (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (m : ↥(M.vertexFixed (Γ.vertexRep i))) :
    phiPre M ch m
      = M.φEdge' (ch.τ⁻¹ • Γ.edgeRep ε) ch.tauSource.symm (target_tau_inv_edgeRep ch)
          (M.φ' (ch.τ⁻¹ * ch.σ) rfl (m : M.M (Γ.vertexRep i))) := by
  have h1 : ch.τ⁻¹ • Γ.toRQuiver.source (Γ.edgeRep ε)
      = (ch.τ⁻¹ * ch.σ) • Γ.vertexRep i := by
    rw [← ch.source_eq, ← mul_smul]
  have key := M.φEdge'_φ' ch.τ⁻¹ (rfl : ch.τ⁻¹ • Γ.edgeRep ε = ch.τ⁻¹ • Γ.edgeRep ε)
    (rfl : Γ.toRQuiver.source (Γ.edgeRep ε) = _)
    (rfl : Γ.toRQuiver.target (Γ.edgeRep ε) = _)
    ch.tauSource.symm (target_tau_inv_edgeRep ch) h1 ch.tauTarget
    (M.φ' ch.σ ch.sourceVertex (m : M.M (Γ.vertexRep i)))
  rw [phiPre, ← key]
  congr 1
  exact M.φ'_comp ch.τ⁻¹ ch.σ ch.sourceVertex h1 rfl (m : M.M (Γ.vertexRep i))

/-- `phiPre` is fixed by `G_{τ_ε⁻¹ e_ε}`. -/
theorem phiPre_fixed (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (m : ↥(M.vertexFixed (Γ.vertexRep i)))
    {g : Gal(L/K)} (hg : g ∈ stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε))
    (hgj : g • Γ.vertexRep j = Γ.vertexRep j) :
    M.φ' g hgj (phiPre M ch m) = phiPre M ch m := by
  have hgs : g • ((ch.τ⁻¹ * ch.σ) • Γ.vertexRep i) = (ch.τ⁻¹ * ch.σ) • Γ.vertexRep i := by
    rw [ch.tauSource]; exact Γ.stabilizer_le_source _ hg
  have hinner : M.φ' g hgs (M.φ' (ch.τ⁻¹ * ch.σ) rfl (m : M.M (Γ.vertexRep i)))
      = M.φ' (ch.τ⁻¹ * ch.σ) rfl (m : M.M (Γ.vertexRep i)) := by
    have hcomb : (g * (ch.τ⁻¹ * ch.σ)) • Γ.vertexRep i
        = (ch.τ⁻¹ * ch.σ) • Γ.vertexRep i := by rw [mul_smul, hgs]
    rw [M.φ'_comp g (ch.τ⁻¹ * ch.σ) rfl hgs hcomb (m : M.M (Γ.vertexRep i))]
    exact M.φ'_insert_of_vertexFixed_aux m (ch.τ⁻¹ * ch.σ) g hgs hcomb rfl
  have key := M.φEdge'_φ' g hg
    ch.tauSource.symm (target_tau_inv_edgeRep ch)
    ch.tauSource.symm (target_tau_inv_edgeRep ch) hgs hgj
    (M.φ' (ch.τ⁻¹ * ch.σ) rfl (m : M.M (Γ.vertexRep i)))
  rw [phiPre_eq, ← key, hinner]

/-- `rep η` stabilises `v_j`. -/
theorem EdgeChoice.rep_mem {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch) :
    EdgeChoice.rep Γ ch η • Γ.vertexRep j = Γ.vertexRep j :=
  (Quotient.out η : stabilizer Gal(L/K) (Γ.vertexRep j)).2

/-- `phiComp` factors through `phiPre`: apply `τ_ε⁻¹` first, then the coset representative. -/
theorem phiComp_eq_phiPre (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch)
    (m : ↥(M.vertexFixed (Γ.vertexRep i))) :
    phiComp M ch η m
      = M.φ' (EdgeChoice.rep Γ ch η) (ch.rep_mem η) (phiPre M ch m) :=
  (M.φ'_comp (EdgeChoice.rep Γ ch η) ch.τ⁻¹ ch.tauTarget (ch.rep_mem η)
    (ch.cosetTarget η) _).symm

/-- `g ∈ G_{τ_ε⁻¹ e_ε}` fixes `v_j`. -/
theorem EdgeChoice.stab_fixes_vertexRep {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) {g : Gal(L/K)}
    (hg : g ∈ stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε)) :
    g • Γ.vertexRep j = Γ.vertexRep j := by
  have := Γ.stabilizer_le_target _ hg
  rwa [target_tau_inv_edgeRep ch] at this

/-- **`Φ`'s componentwise equivariance.**  `φ'_σ` moves the `η`-component to the `σ·η`-component. -/
theorem phiComp_smul_index (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)))
    (η : EdgeChoice.CosetIndex Γ ch) (m : ↥(M.vertexFixed (Γ.vertexRep i))) :
    M.φ' (σ : Gal(L/K)) σ.2 (phiComp M ch η m) = phiComp M ch (σ • η) m := by
  obtain ⟨g, hg, hgeq⟩ := ch.rep_smul_eq σ (σ • η)
  rw [inv_smul_smul] at hgeq
  have hgj := ch.stab_fixes_vertexRep hg
  have hmul : (EdgeChoice.rep Γ ch (σ • η) * g) • Γ.vertexRep j = Γ.vertexRep j := by
    rw [mul_smul, hgj, ch.rep_mem]
  rw [phiComp_eq_phiPre, phiComp_eq_phiPre,
    M.φ'_comp (σ : Gal(L/K)) (EdgeChoice.rep Γ ch η) (ch.rep_mem η) σ.2
      (show ((σ : Gal(L/K)) * EdgeChoice.rep Γ ch η) • Γ.vertexRep j = Γ.vertexRep j by
        rw [mul_smul, ch.rep_mem, σ.2]),
    M.φ'_congr hgeq _ hmul,
    ← M.φ'_comp (EdgeChoice.rep Γ ch (σ • η)) g hgj (ch.rep_mem (σ • η)) hmul,
    phiPre_fixed M ch m hg hgj]

/-- The scalar half: the twist `η τ_ε⁻¹` transforms the same way. -/
theorem EdgeChoice.smul_twist_apply {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)))
    (η : EdgeChoice.CosetIndex Γ ch) (c : ↥(Γ.edgeOrbitField ε)) :
    (σ : Gal(L/K)) ((EdgeChoice.rep Γ ch η * ch.τ⁻¹) (c : L))
      = (EdgeChoice.rep Γ ch (σ • η) * ch.τ⁻¹) (c : L) := by
  obtain ⟨g, hg, hgeq⟩ := ch.rep_smul_eq σ (σ • η)
  rw [inv_smul_smul] at hgeq
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply,
    show (σ : Gal(L/K)) ((EdgeChoice.rep Γ ch η) (ch.τ⁻¹ (c : L)))
      = ((σ : Gal(L/K)) * EdgeChoice.rep Γ ch η) (ch.τ⁻¹ (c : L)) from
      (AlgEquiv.mul_apply _ _ _).symm, hgeq, AlgEquiv.mul_apply,
    fix_of_mem_stabilizer_tau ch hg c]

theorem phiComp_zero (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch) :
    phiComp M ch η 0 = 0 := by
  show M.φ' _ _ (M.φEdge' _ _ _ (M.φ' _ _ ((0 : ↥(M.vertexFixed (Γ.vertexRep i)))
    : M.M (Γ.vertexRep i)))) = 0
  rw [show (((0 : ↥(M.vertexFixed (Γ.vertexRep i))) : M.M (Γ.vertexRep i))) = 0 from rfl,
    map_zero, map_zero, map_zero]

theorem phiComp_add (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch)
    (m m' : ↥(M.vertexFixed (Γ.vertexRep i))) :
    phiComp M ch η (m + m') = phiComp M ch η m + phiComp M ch η m' := by
  show M.φ' _ _ (M.φEdge' _ _ _ (M.φ' _ _ (((m + m' : ↥(M.vertexFixed (Γ.vertexRep i)))
    : M.M (Γ.vertexRep i))))) = _
  rw [show (((m + m' : ↥(M.vertexFixed (Γ.vertexRep i))) : M.M (Γ.vertexRep i)))
      = (m : M.M (Γ.vertexRep i)) + (m' : M.M (Γ.vertexRep i)) from rfl,
    map_add, map_add, map_add]
  rfl

theorem phiComp_smul_base (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch)
    (b : ↥(Γ.vertexOrbitField i)) (m : ↥(M.vertexFixed (Γ.vertexRep i))) :
    phiComp M ch η (b • m)
      = ((EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ) (b : L)) • phiComp M ch η m := by
  show M.φ' _ _ (M.φEdge' _ _ _ (M.φ' _ _ (((b • m : ↥(M.vertexFixed (Γ.vertexRep i)))
    : M.M (Γ.vertexRep i))))) = _
  rw [show (((b • m : ↥(M.vertexFixed (Γ.vertexRep i))) : M.M (Γ.vertexRep i)))
      = (b : L) • (m : M.M (Γ.vertexRep i)) from rfl,
    M.φ'_smul, map_smul, M.φ'_smul, AlgEquiv.mul_apply, AlgEquiv.mul_apply,
    AlgEquiv.mul_apply]
  rfl

/-- The `(ε,η)`-component of `Φ`, as an additive map. -/
noncomputable def phiTensorAdd (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch) :
    (Twist (Γ.vertexOrbitField i) (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ)
      ⊗[Twist.TwistBase (Γ.vertexOrbitField i) (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ)]
        ↥(M.vertexFixed (Γ.vertexRep i))) →+ M.M (Γ.vertexRep j) :=
  TensorProduct.liftAddHom
    { toFun := fun t =>
        { toFun := fun m => t.val • phiComp M ch η m
          map_zero' := by rw [phiComp_zero, smul_zero]
          map_add' := fun m m' => by rw [phiComp_add, smul_add] }
      map_zero' := by
        refine AddMonoidHom.ext fun m => ?_
        show ((0 : Twist (Γ.vertexOrbitField i) _).val) • phiComp M ch η m = 0
        rw [Twist.val_zero, zero_smul]
      map_add' := fun t t' => by
        refine AddMonoidHom.ext fun m => ?_
        show ((t + t').val) • phiComp M ch η m = t.val • phiComp M ch η m
          + t'.val • phiComp M ch η m
        rw [Twist.val_add, add_smul] }
    (fun b t m => by
      show (b • t).val • phiComp M ch η m = t.val • phiComp M ch η (b • m)
      rw [Twist.val_smulL_base,
        show (b • m : ↥(M.vertexFixed (Γ.vertexRep i)))
          = (b.val : ↥(Γ.vertexOrbitField i)) • m from rfl,
        phiComp_smul_base, smul_smul, mul_comm])

@[simp] theorem phiTensorAdd_tmul (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch)
    (t : Twist (Γ.vertexOrbitField i) (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ))
    (m : ↥(M.vertexFixed (Γ.vertexRep i))) :
    phiTensorAdd M ch η
        (t ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
          (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ)] m)
      = t.val • phiComp M ch η m := rfl

/-- …and `L`-linear. -/
noncomputable def phiTensor (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch) :
    (Twist (Γ.vertexOrbitField i) (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ)
      ⊗[Twist.TwistBase (Γ.vertexOrbitField i) (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ)]
        ↥(M.vertexFixed (Γ.vertexRep i))) →ₗ[L] M.M (Γ.vertexRep j) where
  toFun := phiTensorAdd M ch η
  map_add' := map_add _
  map_smul' c z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul t m =>
        show phiTensorAdd M ch η ((c • t) ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
            (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ)] m)
          = c • (t.val • phiComp M ch η m)
        rw [phiTensorAdd_tmul, Twist.val_smulL, smul_smul]
    | add p q hp hq => rw [smul_add, map_add, map_add, hp, hq, smul_add]

section Assembly24

variable (M : Rep Γ) {i j : Γ.VertexOrbit}

/-- The `(ε,η)`-summand of `eq:WiiMjLpre`. -/
@[reducible] noncomputable def preSummand {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε)
    (η : EdgeChoice.CosetIndex Γ ch) : Type u :=
  Twist (Γ.vertexOrbitField i) (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ)
    ⊗[Twist.TwistBase (Γ.vertexOrbitField i) (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ)]
      ↥(M.vertexFixed (Γ.vertexRep i))

/-- `Φ` on one edge-orbit summand: the sum over the coset index of the `(ε,η)`-components. -/
noncomputable def phiPi {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε)
    [Fintype (EdgeChoice.CosetIndex Γ ch)] :
    (∀ η : EdgeChoice.CosetIndex Γ ch, preSummand M ch η) →ₗ[L] M.M (Γ.vertexRep j) :=
  ∑ η : EdgeChoice.CosetIndex Γ ch, (phiTensor M ch η) ∘ₗ (LinearMap.proj η)

theorem phiPi_single {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε)
    [Fintype (EdgeChoice.CosetIndex Γ ch)] [DecidableEq (EdgeChoice.CosetIndex Γ ch)]
    (η : EdgeChoice.CosetIndex Γ ch) (x : preSummand M ch η) :
    phiPi M ch (Pi.single (M := fun η => preSummand M ch η) η x) = phiTensor M ch η x := by
  rw [phiPi, LinearMap.sum_apply]
  rw [Finset.sum_eq_single η]
  · show phiTensor M ch η (Pi.single (M := fun η => preSummand M ch η) η x η) = _
    rw [Pi.single_eq_same]
  · intro η' _ hne
    show phiTensor M ch η' (Pi.single (M := fun η => preSummand M ch η) η x η') = 0
    rw [Pi.single_eq_of_ne hne, map_zero]
  · intro h; exact absurd (Finset.mem_univ η) h

open scoped Classical in
/-- **`Φ_{ij}`** — the map of clause `RQ2-2.24-H1`.

`open scoped Classical in` throughout this block, deliberately: `DirectSum.lof` needs
`DecidableEq (Γ.EdgeOrbit i j)`, and `RQ2-2.24`'s own statement — elaborated under
`open scoped Classical` — resolves it to `Quotient.decidableEq` through classical decidability of
the orbit relation.  A `[DecidableEq …]` **binder** here produces a different instance, and the
two `DirectSum.lof` terms are then equal-but-not-defeq: measured, as a `Type mismatch` between two
goals that print identically until `pp.explicit` shows `fun a b => Quotient.decidableEq a b`
against `inst✝`.  This is `CONVENTIONS.md` §3's instance family in its `DecidableEq` form. -/
noncomputable def phiTotal (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε))] :
    wiiMjLpreRhs M ch →ₗ[L] M.M (Γ.vertexRep j) :=
  DirectSum.toModule L _ _ (fun ε => phiPi M (ch ε))

open scoped Classical in
theorem phiTotal_lof (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε))]
    (ε : Γ.EdgeOrbit i j)
    (F : ∀ η : EdgeChoice.CosetIndex Γ (ch ε), preSummand M (ch ε) η) :
    phiTotal M ch (DirectSum.lof L _ _ ε F) = phiPi M (ch ε) F :=
  DirectSum.toModule_lof (R := L) (ι := Γ.EdgeOrbit i j)
    (M := fun ε => ∀ η : EdgeChoice.CosetIndex Γ (ch ε), preSummand M (ch ε) η)
    (N := M.M (Γ.vertexRep j)) (φ := fun ε => phiPi M (ch ε)) ε F

open scoped Classical in
/-- **Clause `RQ2-2.24-H1`, the defining formula.**

`open scoped Classical in`, deliberately: `IsEdgeDescent` and `RQ2-2.24`'s own statement are
elaborated that way, so `Pi.single`'s `DecidableEq` must be **the same instance** here or the two
terms are equal-but-not-defeq and no `exact` will bridge them.  Measured, not guessed: with a
`[∀ ε, DecidableEq …]` binder instead, the `exact` in `isEdgeDescent_phiDescentMap` fails on two
goals that print identically. -/
theorem phiTotal_single (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε))]
    (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)) (a : L)
    (m : ↥(M.vertexFixed (Γ.vertexRep i))) :
    phiTotal M ch (DirectSum.lof L _ _ ε
        (Pi.single (M := fun η => preSummand M (ch ε) η) η
          (Twist.ofL a ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
            (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)] m)))
      = a • phiComp M (ch ε) η m := by
  rw [phiTotal_lof, phiPi_single]
  rfl

open scoped Classical in
/-- Two additive maps out of `eq:WiiMjLpre`'s right-hand side that agree on the
`(ε,η)`-components are equal — so `Φ` is determined by clause `RQ2-2.24-H1`, and the `∀ Φ` of
`IsEdgeDescent` quantifies over exactly one map. -/
theorem preRhs_addHom_ext (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε))]
    {N : Type u} [AddCommGroup N]
    {g h : wiiMjLpreRhs M ch →+ N}
    (H : ∀ (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)) (a : L)
        (m : ↥(M.vertexFixed (Γ.vertexRep i))),
      g (DirectSum.lof L _ _ ε (Pi.single (M := fun η => preSummand M (ch ε) η) η
          (Twist.ofL a ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
            (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)] m)))
        = h (DirectSum.lof L _ _ ε (Pi.single (M := fun η => preSummand M (ch ε) η) η
          (Twist.ofL a ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
            (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)] m)))) :
    g = h := by
  refine DirectSum.addHom_ext fun ε F => ?_
  show g (DirectSum.lof L _ _ ε F) = h (DirectSum.lof L _ _ ε F)
  rw [← Finset.univ_sum_single F]
  rw [map_sum (DirectSum.lof L (Γ.EdgeOrbit i j)
      (fun ε => ∀ η : EdgeChoice.CosetIndex Γ (ch ε), preSummand M (ch ε) η) ε),
    map_sum, map_sum]
  refine Finset.sum_congr rfl fun η _ => ?_
  induction (F η) using TensorProduct.induction_on with
  | zero => simp
  | tmul t m =>
      have ht : t = Twist.ofL t.val := rfl
      rw [ht]
      exact H ε η t.val m
  | add p q hp hq =>
      have hsplit : (Pi.single (M := fun η => preSummand M (ch ε) η) η (p + q))
          = Pi.single (M := fun η => preSummand M (ch ε) η) η p
            + Pi.single (M := fun η => preSummand M (ch ε) η) η q := by
        rw [Pi.single_add]
      rw [hsplit, map_add, map_add, map_add, hp, hq]

open scoped Classical in
/-- **Clause `RQ2-2.24-C1`**: `Φ_{ij}` is `G_{v_j}`-equivariant for
`eq:explicitdecompositiontwisting`. -/
theorem phiTotal_equivariant (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε))]
    (Θ' : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)) →
      (wiiMjLpreRhs M ch ≃+ wiiMjLpreRhs M ch))
    (hΘ : ∀ (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) (ε : Γ.EdgeOrbit i j)
        (η : EdgeChoice.CosetIndex Γ (ch ε)) (a : L)
        (m : ↥(M.vertexFixed (Γ.vertexRep i))),
      Θ' σ (DirectSum.lof L _ _ ε (Pi.single η (Twist.ofL a ⊗ₜ m)))
        = DirectSum.lof L _ _ ε
            (Pi.single (σ • η) (Twist.ofL ((σ : Gal(L/K)) a) ⊗ₜ m)))
    (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) (x : wiiMjLpreRhs M ch) :
    phiTotal M ch (Θ' σ x) = M.φ' (σ : Gal(L/K)) σ.2 (phiTotal M ch x) := by
  have key : ((phiTotal M ch).toAddMonoidHom.comp (Θ' σ).toAddMonoidHom)
      = ((M.φ' (σ : Gal(L/K)) σ.2).toAddMonoidHom.comp (phiTotal M ch).toAddMonoidHom) := by
    refine preRhs_addHom_ext M ch fun ε η a m => ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      AddEquiv.coe_toAddMonoidHom]
    rw [hΘ σ ε η a m, phiTotal_single, phiTotal_single, M.φ'_smul,
      phiComp_smul_index M (ch ε) σ η m]
  exact DFunLike.congr_fun key x

end Assembly24

open scoped Classical in
/-- **The pre-`S5-F8` shape of `IsEdgeDescent`, kept as the finding's evidence.**

This is `IsEdgeDescent`'s body *before* the `S5-F8` repair — the identification `e₀` unconstrained.
The three theorems below are stated against it, because the finding is about **this** predicate;
restating them against the repaired one would be false, which is precisely the repair working.
Nothing in the development consumes `IsEdgeDescentUnpinned`; it exists so that §56's entailment
stays checkable, per the `S5-F6` precedent (§48).

@census none (finding `S5-F8`, evidence) -/
def IsEdgeDescentUnpinned (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j))) : Prop :=
  ∀ Φ : wiiMjLpreRhs M ch →ₗ[L] M.M (Γ.vertexRep j),
    (∀ (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)) (a : L)
        (m : ↥(M.vertexFixed (Γ.vertexRep i))),
      Φ (DirectSum.lof L _ _ ε (Pi.single η (Twist.ofL a ⊗ₜ m)))
        = a • phiComp M (ch ε) η m) →
    ∀ (t : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))) (a : L),
      Φ (e₀ (Balanced.mk t a)) = a • ((f t : M.M (Γ.vertexRep j)))

open scoped Classical in
/-- **`f` is the Galois descent of `Φ_{ij}` along THE canonical identification** — clause
`RQ2-2.24-C2`'s relation, named because `RQ2-2.25-C4` and `RQ2-2.26` need to speak about it too.

Two conjuncts:

* **`e₀` is `RQ2-2.20-C1`'s identification** — it satisfies that clause's pin.  By
  `wiiMjPre_pin_unique` the pin determines `e₀` outright, so this says "the canonical one", which
  is what the source means by *the* decomposition;
* **`f` descends `Φ` along it**: `f ⊗ 1_L = Φ`, which on the pure tensors of
  `W_i ⊗_{L_i} {}_iM_j ⊗_{L_j} L` reads `Φ(e₀(t ⊗ a)) = a · ι(f t)`, for **every** `Φ` satisfying
  `RQ2-2.24-H1`'s componentwise formula — a universal that collapses, since `preRhs_addHom_ext`
  shows `H1` determines `Φ`.

**The first conjunct is finding `S5-F8`'s repair** (§56.4 option (b), coordinator-sanctioned).
Without it `e₀` is unconstrained, and `IsEdgeDescentUnpinned` above is stable under scaling
`(e₀, f)` by a unit of `L(v_j)` (`isEdgeDescent_smul`) — which collapses every clause of the form
`∀ e₀ f, IsEdgeDescent … → <equation pinning f against something f-independent>` to `f = 0`.
Pinning `e₀` closes that at its source and costs nothing: `RQ2-2.24`'s own witness comes from
`RQ2-2.20-C1` and therefore already carries the pin.

@census none (clause witness for `RQ2-2.24-C2`)
@clauses   RQ2-2.24-C2
-/
def IsEdgeDescent (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j))) : Prop :=
  (∀ (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) (a : L)
      (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)),
    e₀ (Balanced.mk (Balanced.mk w m) a) ε η
      = Twist.ofL (a * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹) ((m ε : L)))
          ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
              (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)] w) ∧
  ∀ Φ : wiiMjLpreRhs M ch →ₗ[L] M.M (Γ.vertexRep j),
    (∀ (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)) (a : L)
        (m : ↥(M.vertexFixed (Γ.vertexRep i))),
      Φ (DirectSum.lof L _ _ ε (Pi.single η (Twist.ofL a ⊗ₜ m)))
        = a • phiComp M (ch ε) η m) →
    ∀ (t : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))) (a : L),
      Φ (e₀ (Balanced.mk t a)) = a • ((f t : M.M (Γ.vertexRep j)))


/-! ### Finding **`S5-F8`**, compiled — `IsEdgeDescent`'s identification is unpinned

`IsEdgeDescent M ch e₀ f` constrains `f` **relative to `e₀`**, and nothing constrains `e₀`.  The
binder type `wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch` is closed under post-composition with `c • ·`
for any `c ∈ L`, and when `c` is taken in **`L(v_j)`** — not in `L` — the scaled `f` still lands in
`W_j = M(v_j)^{G_{v_j}}`, so the *pair* `(c·e₀, c·f)` satisfies `IsEdgeDescent` whenever `(e₀, f)`
does.  That is `isEdgeDescent_smul` below, and it is the whole finding.

**Why this is not `V-S5b-16` re-opened, and why the S5b delta pass could not see it.**  `V-S5b-16`
refuted `∀ e₀, ∃ f` by scaling with a `b ∈ L` that `G_{v_j}` **moves**; the verifier's §D.3d check
then cleared the four `∀ e₀ f, IsEdgeDescent … → …` clauses on exactly the ground that such a
scaling *breaks* `W_j`-membership, so the hypothesis becomes unsatisfiable and the clause says
nothing — the sound behaviour.  That reasoning is right for `b ∉ L(v_j)` and **fails for
`c ∈ L(v_j)`**, where `W_j`-membership is preserved and the hypothesis stays satisfiable.  The two
scalings are complementary halves of one binder type, and only one half was checked.

**Consequence, measured below rather than argued.**  Any clause of the form
`∀ e₀ f, IsEdgeDescent M ch e₀ f → <equation pinning f's value against something f-independent>`
forces that value to be `0` as soon as `L(v_j)` has a unit other than `1`.

@census none (finding `S5-F8`, statement-layer; reported, no repair — statements are frozen)
-/

/-- **The `S5-F8` repair, certified as a strengthening.**  `#check` cannot see this: `IsEdgeDescent`
is a `def` into `Prop`, so its *type* — and the elaborated signature of all five rows that name it
— is **byte-identical** before and after the repair, and only the body changed.  What did change is
exactly one added conjunct, and this is that statement, compiled: the repaired predicate implies
the pre-repair one, by first projection.

The converse is *not* provable, and must not be: `isEdgeDescent_smul` below is a counterexample
generator for it.  Together the two say precisely what the repair did.

@census none (certificate for the `S5-F8` repair) -/
theorem isEdgeDescent_le_unpinned (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j)))
    (h : IsEdgeDescent M ch e₀ f) : IsEdgeDescentUnpinned M ch e₀ f := h.2

/-- **`S5-F8`, step 1.**  `IsEdgeDescent` is stable under scaling the identification by a nonzero
element of `L(v_j)` — scaling the descent by the same element.

`L(v_j)` is the point: for `c ∈ L(v_j)` the scaled descent still lands in `W_j`, because `W_j` is an
`L(v_j)`-module.  For a general `c ∈ L` it does not, which is `V-S5b-16`'s half of the same binder
type.

@census none (helper; finding `S5-F8`) -/
theorem isEdgeDescent_smul (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j)))
    (c : ↥(Γ.vertexOrbitField j)) (hc : (c : L) ≠ 0)
    (h : IsEdgeDescentUnpinned M ch e₀ f) :
    IsEdgeDescentUnpinned M ch
      (e₀ ≪≫ₗ LinearEquiv.smulOfNeZero L (wiiMjLpreRhs M ch) (c : L) hc)
      ((MulOpposite.op c : (Γ.toSpecies.L j)ᵐᵒᵖ) • f) := by
  intro Φ hΦ t a
  show Φ ((c : L) • e₀ (Balanced.mk t a)) = _
  rw [map_smul, h Φ hΦ t a]
  show (c : L) • (a • ((f t : M.M (Γ.vertexRep j))))
    = a • ((c : L) • ((f t : M.M (Γ.vertexRep j))))
  rw [smul_comm]

/-- **`S5-F8`, step 2 — the general collision, compiled.**  A clause quantifying
`∀ e₀ f, IsEdgeDescent M ch e₀ f → …` whose conclusion pins `F1 (f (w ⊗ m))` to something
**independent of `f`** forces `f (w ⊗ m) = 0`, provided `L(v_j)` has a unit other than `1`.

Two instantiations of the clause — at `(e₀, f)` and at `(c·e₀, c·f)`, both legitimate by step 1 —
give `F1 (c · f (w ⊗ m)) = F1 (f (w ⊗ m))`, and injectivity of `F1` then makes `f (w ⊗ m)` a fixed
point of multiplication by `c ≠ 1`.

**This shape is `RQ2-2.26-C1`, `RQ2-2.28-H2`(a) and `RQ2-2.29`'s `hF1`/`hH1`** — with `F1` the
identification `eF M j` / `e_fix V j` (injective, being an equivalence) and the `f`-independent side
`(F.obj M).f i j (…)` resp. `V`'s own structure map.  In `RQ2-2.26`/`RQ2-2.28` those are conclusions,
so the rows are **over-strong**; in `RQ2-2.29` they are hypotheses, so the row is **vacuous** to the
same extent.

@census none (finding `S5-F8`, compiled entailment) -/
theorem isEdgeDescent_universal_forces_zero (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε) {X Z : Type u}
    (F1 : ↥(M.vertexFixed (Γ.vertexRep j)) → Z) (hF1inj : Function.Injective F1)
    (G1 : X → Γ.toSpecies.M i j → Z)
    (hh : X → ↥(M.vertexFixed (Γ.vertexRep i)))
    (hC : ∀ (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
        (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
              →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j))),
      IsEdgeDescentUnpinned M ch e₀ f → ∀ (w : X) (m : Γ.toSpecies.M i j),
        F1 (f (Balanced.mk (hh w) m)) = G1 w m)
    (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j)))
    (h : IsEdgeDescentUnpinned M ch e₀ f)
    (c : ↥(Γ.vertexOrbitField j)) (hc : (c : L) ≠ 0) (hc1 : (c : L) ≠ 1)
    (w : X) (m : Γ.toSpecies.M i j) :
    f (Balanced.mk (hh w) m) = 0 := by
  have h1 := hC e₀ f h w m
  have h2 := hC (e₀ ≪≫ₗ LinearEquiv.smulOfNeZero L (wiiMjLpreRhs M ch) (c : L) hc)
      ((MulOpposite.op c : (Γ.toSpecies.L j)ᵐᵒᵖ) • f)
      (isEdgeDescent_smul M ch e₀ f c hc h) w m
  have h3 : ((MulOpposite.op c : (Γ.toSpecies.L j)ᵐᵒᵖ) • f) (Balanced.mk (hh w) m)
      = f (Balanced.mk (hh w) m) := hF1inj (h2.trans h1.symm)
  have h4 : ((f (Balanced.mk (hh w) m) : M.M (Γ.vertexRep j)))
      = (c : L) • ((f (Balanced.mk (hh w) m) : M.M (Γ.vertexRep j))) :=
    (congrArg Subtype.val h3).symm
  have h5 : ((1 : L) - (c : L)) • ((f (Balanced.mk (hh w) m) : M.M (Γ.vertexRep j))) = 0 := by
    rw [sub_smul, one_smul, ← h4, sub_self]
  refine Subtype.ext ?_
  rcases smul_eq_zero.mp h5 with h6 | h6
  · exact absurd (by linear_combination -h6 : (c : L) = 1) hc1
  · exact h6

/-- **`S5-F8`, step 3 — `RQ2-2.25-C4` in particular.**  The row's `C4`, taken at `N := M` and
`ψ := 𝟙` (where `C2`'s characterisation forces `ψ' = id`), entails that **every** edge descent is
zero on generators.

Two instantiations of `C4` — `(eM, fM) := (e₀, f)` and `(eM, fM) := (c·e₀, c·f)`, with `(eN, fN)`
held at `(e₀, f)` both times — give `f (w ⊗ m) = c · f (w ⊗ m)`.

Combined with `RQ2-2.24-C2`'s `∃ e₀ f, IsEdgeDescent` and `IsEdgeDescent`'s own equation
`Φ (e₀ (t ⊗ a)) = a · ι(f t)`, this makes `Φ` vanish on the `mk`-image of a surjection, i.e. `Φ = 0`
— contradicting `RQ2-2.24-H1` for any `M` with a non-zero `phiComp`.  The honest grading is therefore
**unprovable as frozen**, exactly as for `S5-F6`: what is compiled is the entailment, not a
counterexample.

@census none (finding `S5-F8`, compiled entailment) -/
theorem F_map_C4_entails_edgeDescent_zero (M : Rep Γ)
    (ψ' : ∀ i : Γ.VertexOrbit,
      ↥(M.vertexFixed (Γ.vertexRep i)) →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ]
        ↥(M.vertexFixed (Γ.vertexRep i)))
    (hψ' : ∀ (i : Γ.VertexOrbit) (m : ↥(M.vertexFixed (Γ.vertexRep i))),
      ((ψ' i m : M.M (Γ.vertexRep i)))
        = (Rep.Hom.id M).ψ (Γ.vertexRep i) (m : M.M (Γ.vertexRep i)))
    (hC4 : ∀ (i j : Γ.VertexOrbit) (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
        (eM : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
        (eN : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
        (fM : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
              →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j)))
        (fN : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
              →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j))),
        IsEdgeDescentUnpinned M ch eM fM → IsEdgeDescentUnpinned M ch eN fN →
        ∀ (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j),
          fN (Balanced.mk (ψ' i w) m) = ψ' j (fM (Balanced.mk w m)))
    {i j : Γ.VertexOrbit} (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j)))
    (h : IsEdgeDescentUnpinned M ch e₀ f)
    (c : ↥(Γ.vertexOrbitField j)) (hc : (c : L) ≠ 0) (hc1 : (c : L) ≠ 1)
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) :
    f (Balanced.mk w m) = 0 := by
  have hid : ∀ (k : Γ.VertexOrbit) (x : ↥(M.vertexFixed (Γ.vertexRep k))), ψ' k x = x := by
    intro k x
    apply Subtype.ext
    rw [hψ']
    rfl
  have h2 := hC4 i j ch (e₀ ≪≫ₗ LinearEquiv.smulOfNeZero L (wiiMjLpreRhs M ch) (c : L) hc)
      e₀ ((MulOpposite.op c : (Γ.toSpecies.L j)ᵐᵒᵖ) • f) f
      (isEdgeDescent_smul M ch e₀ f c hc h) h w m
  rw [hid, hid] at h2
  have h3 : ((f (Balanced.mk w m) : M.M (Γ.vertexRep j)))
      = (c : L) • ((f (Balanced.mk w m) : M.M (Γ.vertexRep j))) := congrArg Subtype.val h2
  have h4 : ((1 : L) - (c : L)) • ((f (Balanced.mk w m) : M.M (Γ.vertexRep j))) = 0 := by
    rw [sub_smul, one_smul, ← h3, sub_self]
  refine Subtype.ext ?_
  rcases smul_eq_zero.mp h4 with h5 | h5
  · exact absurd (by linear_combination -h5 : (c : L) = 1) hc1
  · exact h5

/-! ### `RQ2-2.24` — `Φ_{ij}` descends  (G4)

Clause `C2`/`C3` is Galois descent, and the only thing it needs beyond `RQ2-2.23` is that
`Φ ∘ e₀` **lands in `W_j`**.  That is proved here directly on generators rather than by building a
second rational structure on `eq:WiiMjLpre`'s right-hand side and invoking `C1`: `RQ2-2.20-C1`'s
pin evaluates `e₀` on `(w ⊗ m) ⊗ a`, `phiTotal_apply`/`phiPi_apply` turn `Φ` into the double sum
`∑_ε ∑_η (a·(ητ_ε⁻¹)(m_ε)) · φ_{ε,η}(w)` the source displays, and the two halves of the
equivariance (`phiComp_smul_index`, `EdgeChoice.smul_twist_apply`) move `σ` through it as a
**reindexing** `η ↦ σ·η`.  At `a = 1` the reindexed sum is the original, which is the invariance.

So the source's `eq:explicitdecompositiontwisting` is used exactly where the source uses it, and
`Θ'` never has to be constructed — `C1` quantifies over any `Θ'` with the right pin, and the
descent needs only the identity at `a = 1`.

The descended `f_{ij}` is then `t ↦ Φ (e₀ (t ⊗ 1))`, whose `L_j`-linearity is `Balanced.mk_smul`
plus the value guard `balanced_smul_L_mk`, and `IsEdgeDescent`'s universal over `Φ` collapses by
`preRhs_addHom_ext`.

@census none (G4 engine for `RQ2-2.24-C2`)
-/

section C2
variable (M : Rep Γ) {i j : Γ.VertexOrbit}

theorem phiPi_apply {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε)
    [Fintype (EdgeChoice.CosetIndex Γ ch)]
    (F : ∀ η : EdgeChoice.CosetIndex Γ ch, preSummand M ch η) :
    phiPi M ch F = ∑ η : EdgeChoice.CosetIndex Γ ch, phiTensor M ch η (F η) := by
  rw [phiPi, LinearMap.sum_apply]
  rfl

open scoped Classical in
theorem phiTotal_apply (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε))]
    (x : wiiMjLpreRhs M ch) :
    phiTotal M ch x = ∑ ε : Γ.EdgeOrbit i j, phiPi M (ch ε) (x ε) := by
  conv_lhs => rw [← DirectSum.sum_univ_of x]
  rw [map_sum]
  exact Finset.sum_congr rfl fun ε _ => phiTotal_lof M ch ε (x ε)

theorem phiTensor_ofL (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch) (c : L)
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) :
    phiTensor M ch η (Twist.ofL c ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
        (EdgeChoice.rep Γ ch η * ch.τ⁻¹ * ch.σ)] w) = c • phiComp M ch η w := rfl

variable [Fintype (Γ.EdgeOrbit i j)]

open scoped Classical in
theorem phiTotal_e0_generator (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε))]
    (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (h₀ : ∀ (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) (a : L)
        (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)),
      e₀ (Balanced.mk (Balanced.mk w m) a) ε η
        = Twist.ofL (a * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹) ((m ε : L)))
            ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
                (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)] w)
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) (a : L) :
    phiTotal M ch (e₀ (Balanced.mk (Balanced.mk w m) a))
      = ∑ ε : Γ.EdgeOrbit i j, ∑ η : EdgeChoice.CosetIndex Γ (ch ε),
          (a * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹) ((m ε : L)))
            • phiComp M (ch ε) η w := by
  rw [phiTotal_apply]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [phiPi_apply]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [h₀ w m a ε η]
  exact phiTensor_ofL M (ch ε) η _ w

open scoped Classical in
theorem phiTotal_e0_smul (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε))]
    (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (h₀ : ∀ (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) (a : L)
        (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)),
      e₀ (Balanced.mk (Balanced.mk w m) a) ε η
        = Twist.ofL (a * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹) ((m ε : L)))
            ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
                (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)] w)
    (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)))
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) (a : L) :
    M.φ' (σ : Gal(L/K)) σ.2 (phiTotal M ch (e₀ (Balanced.mk (Balanced.mk w m) a)))
      = phiTotal M ch (e₀ (Balanced.mk (Balanced.mk w m) ((σ : Gal(L/K)) a))) := by
  rw [phiTotal_e0_generator M ch e₀ h₀, phiTotal_e0_generator M ch e₀ h₀, map_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm σ) _ _ ?_
  intro η
  rw [M.φ'_smul, phiComp_smul_index M (ch ε) σ η w, map_mul,
    EdgeChoice.smul_twist_apply (ch ε) σ η (m ε)]
  rfl

/-- Induction over the generators of `W_i ⊗_{L_i} {}_iM_j`. -/
theorem repTensor_induction {P : EtaleSpecies.Rep.tensor Γ.toSpecies i j
      ↥(M.vertexFixed (Γ.vertexRep i)) → Prop}
    (h0 : P 0)
    (hmk : ∀ (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j),
      P (Balanced.mk w m))
    (hadd : ∀ x y, P x → P y → P (x + y))
    (t : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))) : P t := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective
    (balancedRel K (Γ.toSpecies.L i) (Γ.toSpecies.L j) (Γ.toSpecies.M i j)
      ↥(M.vertexFixed (Γ.vertexRep i))) t
  induction s with
  | zero => simpa using h0
  | tmul m w => exact hmk w m
  | add p q hp hq =>
      have hp2 : (Submodule.Quotient.mk (p := balancedRel K (Γ.toSpecies.L i)
          (Γ.toSpecies.L j) (Γ.toSpecies.M i j) ↥(M.vertexFixed (Γ.vertexRep i))) (p + q))
          = Submodule.Quotient.mk p + Submodule.Quotient.mk q := rfl
      rw [hp2]; exact hadd _ _ hp hq

open scoped Classical in
/-- `Φ ∘ e₀` lands in `W_j`: the `G_{v_j}`-invariance that Galois descent needs. -/
theorem phiTotal_e0_fixed (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε))]
    (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (h₀ : ∀ (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) (a : L)
        (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)),
      e₀ (Balanced.mk (Balanced.mk w m) a) ε η
        = Twist.ofL (a * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹) ((m ε : L)))
            ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
                (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)] w)
    (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)))
    (t : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))) :
    M.φ' (σ : Gal(L/K)) σ.2 (phiTotal M ch (e₀ (Balanced.mk t 1)))
      = phiTotal M ch (e₀ (Balanced.mk t 1)) := by
  induction t using repTensor_induction with
  | h0 =>
      have hz : Balanced.mk (K := K) (A := Γ.toSpecies.L j) (B := L)
          (0 : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i)))
          (1 : L) = 0 := Balanced.mk_zero_left _
      rw [hz, map_zero, map_zero, map_zero]
  | hmk w m =>
      rw [phiTotal_e0_smul M ch e₀ h₀ σ w m 1, map_one]
  | hadd p q hp hq =>
      have hsplit : Balanced.mk (K := K) (A := Γ.toSpecies.L j) (B := L) (p + q) (1 : L)
          = Balanced.mk p (1 : L) + Balanced.mk q (1 : L) := Balanced.mk_add_left _ _ _
      rw [hsplit, map_add, map_add, map_add, hp, hq]

open scoped Classical in
/-- The descended map `f_{ij} : W_i ⊗_{L_i} {}_iM_j → W_j`. -/
noncomputable def edgeDescentMap (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε))]
    (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (h₀ : ∀ (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) (a : L)
        (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)),
      e₀ (Balanced.mk (Balanced.mk w m) a) ε η
        = Twist.ofL (a * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹) ((m ε : L)))
            ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
                (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)] w) :
    EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
      →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j)) where
  toFun t := ⟨phiTotal M ch (e₀ (Balanced.mk t 1)),
    fun σ => phiTotal_e0_fixed M ch e₀ h₀ σ t⟩
  map_add' t t' := by
    apply Subtype.ext
    show phiTotal M ch (e₀ (Balanced.mk (t + t') (1 : L))) = _
    rw [show Balanced.mk (K := K) (A := Γ.toSpecies.L j) (B := L) (t + t') (1 : L)
        = Balanced.mk t (1 : L) + Balanced.mk t' (1 : L) from Balanced.mk_add_left _ _ _,
      map_add, map_add]
    rfl
  map_smul' r t := by
    apply Subtype.ext
    show phiTotal M ch (e₀ (Balanced.mk (r • t) (1 : L)))
      = (algebraMap (Γ.toSpecies.L j) L (MulOpposite.unop r))
          • phiTotal M ch (e₀ (Balanced.mk t (1 : L)))
    have hstep : Balanced.mk (K := K) (A := Γ.toSpecies.L j) (B := L) (r • t) (1 : L)
        = (algebraMap (Γ.toSpecies.L j) L (MulOpposite.unop r))
            • Balanced.mk (K := K) (A := Γ.toSpecies.L j) (B := L) t (1 : L) := by
      have h1 := Balanced.mk_smul (K := K) (A := Γ.toSpecies.L j) (B := L)
        (MulOpposite.unop r) t (1 : L)
      rw [MulOpposite.op_unop] at h1
      rw [h1, show (MulOpposite.unop r • (1 : L))
        = (algebraMap (Γ.toSpecies.L j) L (MulOpposite.unop r)) * 1 from Algebra.smul_def _ _]
      rfl
    rw [hstep, map_smul, map_smul]

open scoped Classical in
/-- **Clauses `RQ2-2.24-C2`/`C3`**: `edgeDescentMap` is the Galois descent of `Φ_{ij}`. -/
theorem isEdgeDescent_edgeDescentMap (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε))]
    (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (h₀ : ∀ (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) (a : L)
        (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)),
      e₀ (Balanced.mk (Balanced.mk w m) a) ε η
        = Twist.ofL (a * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹) ((m ε : L)))
            ⊗ₜ[Twist.TwistBase (Γ.vertexOrbitField i)
                (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹ * (ch ε).σ)] w) :
    IsEdgeDescent M ch e₀ (edgeDescentMap M ch e₀ h₀) := by
  refine ⟨h₀, ?_⟩
  intro Φ hΦ t a
  have huniq : Φ.toAddMonoidHom = (phiTotal M ch).toAddMonoidHom := by
    refine preRhs_addHom_ext M ch fun ε η a m => ?_
    simp only [LinearMap.toAddMonoidHom_coe]
    exact (hΦ ε η a m).trans (phiTotal_single M ch ε η a m).symm
  have hΦx : ∀ x, Φ x = phiTotal M ch x := fun x => DFunLike.congr_fun huniq x
  have hsplit : Balanced.mk (K := K) (A := Γ.toSpecies.L j) (B := L) t a
      = a • Balanced.mk (K := K) (A := Γ.toSpecies.L j) (B := L) t (1 : L) := by
    show Balanced.mk (K := K) (A := Γ.toSpecies.L j) (B := L) t a
      = Balanced.mk (K := K) (A := Γ.toSpecies.L j) (B := L) t (a * 1)
    rw [mul_one]
  rw [hΦx, hsplit, map_smul, map_smul]
  rfl

open scoped Classical in
/-- **The edge descent is unique**, given a fixed choice `ch` — and it is `S5-F8`'s repair that
makes this true.

`IsEdgeDescent`'s two conjuncts do all the work: the pin makes `e₀` unique
(`wiiMjPre_pin_unique`), `preRhs_addHom_ext` makes `Φ` unique, and the descent equation at `a = 1`
then reads `ι(f t) = Φ (e₀ (t ⊗ 1))`, which has no freedom left.

**Before the repair this was false**, and refutably so: `isEdgeDescent_smul` produces `c · f` as a
second descent for every unit `c` of `L(v_j)`.  `RQ2-2.26-C1` — *"the structure maps of `F.obj M`
are the descents"*, quantified over **every** descent — is satisfiable only if there is one; so
this lemma is the clause's precondition, and the finding was the obstruction to `F` itself.

@census none (helper for `RQ2-2.26-C1`) -/
theorem edgeDescent_unique (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₁ e₂ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (f₁ f₂ : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j)))
    (h₁ : IsEdgeDescent M ch e₁ f₁) (h₂ : IsEdgeDescent M ch e₂ f₂) : f₁ = f₂ := by
  classical
  letI : Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
  letI : ∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε)) :=
    fun ε => @Fintype.ofFinite _ (finite_cosetIndex (ch ε))
  refine LinearMap.ext fun t => Subtype.ext ?_
  have hv1 := h₁.2 (phiTotal M ch) (phiTotal_single M ch) t 1
  have hv2 := h₂.2 (phiTotal M ch) (phiTotal_single M ch) t 1
  rw [one_smul] at hv1 hv2
  rw [← hv1, ← hv2, wiiMjPre_pin_unique M ch e₁ e₂ h₁.1 h₂.1]

/-! ### `RQ2-2.26-C1`'s `∀ ch` — the descent does not depend on the §2.6 choice  (G4)

Clause `RQ2-2.26-C1` says the structure maps of `F.obj M` **are** the descents, quantified over
every `ch`.  So it asserts that the descent is independent of the §2.6 preamble choice
`(σ_ε, τ_ε)` — not merely of the identification, which is `edgeDescent_unique`.

**One argument, a fourth time.**  `phiAt` is `phiComp` with the two translations given as bare
group elements, and the whole content is its two invariances:

* `phiAt_source_indep` — `σ_ε` is determined up to right multiplication by `G_{v_i}`, and that
  cancels because `w ∈ W_i` is `G_{v_i}`-invariant.  This is §55.2's device;
* `phiAt_stab` — `phiAt` is unchanged by right multiplication of `g` by `G_{e_ε}`, which is
  §57.1's device with clause `RQ2-1.08-C9` (`Rep.φEdge'_φ'`) doing the transport.

`τ_ε` is determined up to right multiplication by `k ∈ G_{v_j}`, and *that* **conjugates the index
set**: `G_{τ₂⁻¹e} = k⁻¹ G_{τ₁⁻¹e} k`, so the two `CosetIndex`es differ by `η ↦ ηk`
(`EdgeChoice.cosetCongr`) and the two twists differ by an element of `G_{e_ε}`
(`EdgeChoice.rep_tau_congr`) — which the two invariances above then absorb, on the vector
(`phiComp_choice_indep`) and on the scalar (`twist_choice_indep`, where `G_{e_ε}` fixes `L(e_ε)`
by definition of the fixed field).  The two double sums then match term-by-term under the
bijection.

@census none (G4 engine for `RQ2-2.26-C1`)
-/

section ChoiceIndep

variable {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}

/-- `Φ`'s edge composite with the two translations given as bare group elements: `phiComp`
without the `EdgeChoice`. -/
noncomputable def phiAt (M : Rep Γ) {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (g s : Gal(L/K)) (hs : s • Γ.vertexRep i = Γ.toRQuiver.source (Γ.edgeRep ε))
    (hg : g • Γ.toRQuiver.target (Γ.edgeRep ε) = Γ.vertexRep j)
    (m : ↥(M.vertexFixed (Γ.vertexRep i))) : M.M (Γ.vertexRep j) :=
  M.φ' g hg (M.φEdge' (Γ.edgeRep ε) rfl rfl (M.φ' s hs (m : M.M (Γ.vertexRep i))))

/-- **`W_v` is `G_v`-invariant, in transport form**: `φ'_s(w)` does not depend on which `s`
carries `v` to the named target. -/
theorem Rep.φ'_vertexFixed_congr (M : Rep Γ) {v w : Γ.V} (m : ↥(M.vertexFixed v))
    (s s' : Gal(L/K)) (hs : s • v = w) (hs' : s' • v = w) :
    M.φ' s hs (m : M.M v) = M.φ' s' hs' (m : M.M v) := by
  have hu : (s⁻¹ * s') • v = v := by rw [mul_smul, hs', ← hs, inv_smul_smul]
  have hcomb : (s * (s⁻¹ * s')) • v = w := by
    rw [show s * (s⁻¹ * s') = s' by group]; exact hs'
  rw [M.φ'_congr (show s' = s * (s⁻¹ * s') by group) hs' hcomb,
    ← M.φ'_comp s (s⁻¹ * s') hu hs hcomb (m : M.M v),
    show M.φ' (s⁻¹ * s') hu (m : M.M v) = (m : M.M v) from m.2 ⟨s⁻¹ * s', hu⟩]

/-- `phiAt` does not depend on which `s` is used. -/
theorem phiAt_source_indep (M : Rep Γ) {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (g s s' : Gal(L/K)) (hs : s • Γ.vertexRep i = Γ.toRQuiver.source (Γ.edgeRep ε))
    (hs' : s' • Γ.vertexRep i = Γ.toRQuiver.source (Γ.edgeRep ε))
    (hg : g • Γ.toRQuiver.target (Γ.edgeRep ε) = Γ.vertexRep j)
    (m : ↥(M.vertexFixed (Γ.vertexRep i))) :
    phiAt M ε g s hs hg m = phiAt M ε g s' hs' hg m := by
  show M.φ' g hg (M.φEdge' (Γ.edgeRep ε) rfl rfl (M.φ' s hs (m : M.M (Γ.vertexRep i))))
    = M.φ' g hg (M.φEdge' (Γ.edgeRep ε) rfl rfl (M.φ' s' hs' (m : M.M (Γ.vertexRep i))))
  rw [M.φ'_vertexFixed_congr m s s' hs hs']

/-- `phiAt` is unchanged by right multiplication of `g` by an element of `G_{e_ε}`. -/
theorem phiAt_stab (M : Rep Γ) {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (g s : Gal(L/K)) (hs : s • Γ.vertexRep i = Γ.toRQuiver.source (Γ.edgeRep ε))
    {h : Gal(L/K)} (hh : h ∈ stabilizer Gal(L/K) (Γ.edgeRep ε))
    (hg : g • Γ.toRQuiver.target (Γ.edgeRep ε) = Γ.vertexRep j)
    (hgh : (g * h) • Γ.toRQuiver.target (Γ.edgeRep ε) = Γ.vertexRep j)
    (m : ↥(M.vertexFixed (Γ.vertexRep i))) :
    phiAt M ε (g * h) s hs hgh m = phiAt M ε g s hs hg m := by
  have hht : h • Γ.toRQuiver.target (Γ.edgeRep ε) = Γ.toRQuiver.target (Γ.edgeRep ε) :=
    Γ.stabilizer_le_target _ hh
  have hhs : h • Γ.toRQuiver.source (Γ.edgeRep ε) = Γ.toRQuiver.source (Γ.edgeRep ε) :=
    Γ.stabilizer_le_source _ hh
  have hhcomb : (h * s) • Γ.vertexRep i = Γ.toRQuiver.source (Γ.edgeRep ε) := by
    rw [mul_smul, hs, hhs]
  have hedge := M.φEdge'_φ' h hh (rfl : Γ.toRQuiver.source (Γ.edgeRep ε) = _)
    (rfl : Γ.toRQuiver.target (Γ.edgeRep ε) = _)
    (rfl : Γ.toRQuiver.source (Γ.edgeRep ε) = _)
    (rfl : Γ.toRQuiver.target (Γ.edgeRep ε) = _) hhs hht
    (M.φ' s hs (m : M.M (Γ.vertexRep i)))
  show M.φ' (g * h) hgh (M.φEdge' (Γ.edgeRep ε) rfl rfl
      (M.φ' s hs (m : M.M (Γ.vertexRep i)))) = _
  rw [← M.φ'_comp g h hht hg hgh, ← hedge,
    M.φ'_comp h s hs hhs hhcomb (m : M.M (Γ.vertexRep i)),
    M.φ'_vertexFixed_congr m (h * s) s hhcomb hs]
  rfl

theorem stabilizer_conj {X : Type u} [MulAction Gal(L/K) X] (g y : Gal(L/K)) (x : X)
    (hy : y ∈ stabilizer Gal(L/K) x) :
    g * y * g⁻¹ ∈ stabilizer Gal(L/K) (g • x) := by
  rw [mem_stabilizer_iff] at hy ⊢
  rw [mul_smul, mul_smul, inv_smul_smul, hy]


/-- `τ₁⁻¹τ₂` stabilises `v_j`. -/
theorem EdgeChoice.tauRatio_mem (ch₁ ch₂ : Γ.EdgeChoice ε) :
    (ch₁.τ⁻¹ * ch₂.τ) ∈ stabilizer Gal(L/K) (Γ.vertexRep j) := by
  rw [mem_stabilizer_iff, mul_smul, ch₂.target_eq, ← ch₁.target_eq, inv_smul_smul]

/-- `τ₂⁻¹ e_ε = (τ₁⁻¹τ₂)⁻¹ · (τ₁⁻¹ e_ε)`. -/
theorem EdgeChoice.tauEdge_conj (ch₁ ch₂ : Γ.EdgeChoice ε) :
    ch₂.τ⁻¹ • Γ.edgeRep ε = (ch₁.τ⁻¹ * ch₂.τ)⁻¹ • (ch₁.τ⁻¹ • Γ.edgeRep ε) := by
  rw [← mul_smul]
  congr 1
  group

/-- The subgroups of `G_{v_j}` cutting out the two coset spaces are conjugate by `τ₁⁻¹τ₂`. -/
theorem EdgeChoice.subgroupOf_conj (ch₁ ch₂ : Γ.EdgeChoice ε)
    {x : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))}
    (hx : x ∈ (stabilizer Gal(L/K) (ch₁.τ⁻¹ • Γ.edgeRep ε)).subgroupOf
        (stabilizer Gal(L/K) (Γ.vertexRep j)))
    (kk : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)))
    (hkk : (kk : Gal(L/K)) = ch₁.τ⁻¹ * ch₂.τ) :
    kk⁻¹ * x * kk ∈ (stabilizer Gal(L/K) (ch₂.τ⁻¹ • Γ.edgeRep ε)).subgroupOf
      (stabilizer Gal(L/K) (Γ.vertexRep j)) := by
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have : ((kk⁻¹ * x * kk : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) : Gal(L/K))
      = (kk : Gal(L/K))⁻¹ * (x : Gal(L/K)) * ((kk : Gal(L/K))⁻¹)⁻¹ := by
    push_cast; group
  rw [this, EdgeChoice.tauEdge_conj ch₁ ch₂, ← hkk]
  exact stabilizer_conj _ _ _ hx

/-- **The two coset spaces of two §2.6 choices are canonically in bijection**, by right
multiplication by `τ₁⁻¹τ₂`. -/
noncomputable def EdgeChoice.cosetCongr (ch₁ ch₂ : Γ.EdgeChoice ε) :
    EdgeChoice.CosetIndex Γ ch₁ ≃ EdgeChoice.CosetIndex Γ ch₂ := by
  classical
  refine
    { toFun := Quotient.map' (· * ⟨ch₁.τ⁻¹ * ch₂.τ, ch₁.tauRatio_mem ch₂⟩) ?_
      invFun := Quotient.map' (· * ⟨ch₂.τ⁻¹ * ch₁.τ, ch₂.tauRatio_mem ch₁⟩) ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have hr : (a * ⟨ch₁.τ⁻¹ * ch₂.τ, ch₁.tauRatio_mem ch₂⟩)⁻¹
        * (b * ⟨ch₁.τ⁻¹ * ch₂.τ, ch₁.tauRatio_mem ch₂⟩)
        = (⟨ch₁.τ⁻¹ * ch₂.τ, ch₁.tauRatio_mem ch₂⟩ :
            ↥(stabilizer Gal(L/K) (Γ.vertexRep j)))⁻¹ * (a⁻¹ * b)
          * ⟨ch₁.τ⁻¹ * ch₂.τ, ch₁.tauRatio_mem ch₂⟩ := by group
    rw [hr]
    exact ch₁.subgroupOf_conj ch₂ hab _ rfl
  · intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have hr : (a * ⟨ch₂.τ⁻¹ * ch₁.τ, ch₂.tauRatio_mem ch₁⟩)⁻¹
        * (b * ⟨ch₂.τ⁻¹ * ch₁.τ, ch₂.tauRatio_mem ch₁⟩)
        = (⟨ch₂.τ⁻¹ * ch₁.τ, ch₂.tauRatio_mem ch₁⟩ :
            ↥(stabilizer Gal(L/K) (Γ.vertexRep j)))⁻¹ * (a⁻¹ * b)
          * ⟨ch₂.τ⁻¹ * ch₁.τ, ch₂.tauRatio_mem ch₁⟩ := by group
    rw [hr]
    exact ch₂.subgroupOf_conj ch₁ hab _ rfl
  · rintro ⟨a⟩
    show Quotient.map' _ _ (Quotient.map' _ _ (Quotient.mk'' a)) = Quotient.mk'' a
    rw [Quotient.map'_mk'', Quotient.map'_mk'']
    congr 1
    apply Subtype.ext
    show ((a : Gal(L/K)) * (ch₁.τ⁻¹ * ch₂.τ)) * (ch₂.τ⁻¹ * ch₁.τ) = (a : Gal(L/K))
    group
  · rintro ⟨a⟩
    show Quotient.map' _ _ (Quotient.map' _ _ (Quotient.mk'' a)) = Quotient.mk'' a
    rw [Quotient.map'_mk'', Quotient.map'_mk'']
    congr 1
    apply Subtype.ext
    show ((a : Gal(L/K)) * (ch₂.τ⁻¹ * ch₁.τ)) * (ch₁.τ⁻¹ * ch₂.τ) = (a : Gal(L/K))
    group

theorem EdgeChoice.cosetCongr_mk (ch₁ ch₂ : Γ.EdgeChoice ε)
    (a : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) :
    EdgeChoice.cosetCongr ch₁ ch₂ (QuotientGroup.mk a)
      = QuotientGroup.mk (a * ⟨ch₁.τ⁻¹ * ch₂.τ, ch₁.tauRatio_mem ch₂⟩) := rfl

/-- **The two choices' twists differ by an element of `G_{e_ε}`.** -/
theorem EdgeChoice.rep_tau_congr (ch₁ ch₂ : Γ.EdgeChoice ε)
    (η : EdgeChoice.CosetIndex Γ ch₁) :
    ∃ h : Gal(L/K), h ∈ stabilizer Gal(L/K) (Γ.edgeRep ε) ∧
      EdgeChoice.rep Γ ch₂ (EdgeChoice.cosetCongr ch₁ ch₂ η) * ch₂.τ⁻¹
        = EdgeChoice.rep Γ ch₁ η * ch₁.τ⁻¹ * h := by
  classical
  set kk : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)) :=
    ⟨ch₁.τ⁻¹ * ch₂.τ, ch₁.tauRatio_mem ch₂⟩ with hkkdef
  have hmem : (Quotient.out (EdgeChoice.cosetCongr ch₁ ch₂ η))⁻¹ * (Quotient.out η * kk)
      ∈ (stabilizer Gal(L/K) (ch₂.τ⁻¹ • Γ.edgeRep ε)).subgroupOf
          (stabilizer Gal(L/K) (Γ.vertexRep j)) := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' η]
    rw [EdgeChoice.cosetCongr_mk]
  set h₂ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)) :=
    (Quotient.out (EdgeChoice.cosetCongr ch₁ ch₂ η))⁻¹ * (Quotient.out η * kk) with hh₂
  have hout : Quotient.out (EdgeChoice.cosetCongr ch₁ ch₂ η) = Quotient.out η * kk * h₂⁻¹ := by
    rw [hh₂]; group
  refine ⟨ch₂.τ * ((h₂⁻¹ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) : Gal(L/K)) * ch₂.τ⁻¹, ?_, ?_⟩
  · have hs : ((h₂⁻¹ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) : Gal(L/K))
        ∈ stabilizer Gal(L/K) (ch₂.τ⁻¹ • Γ.edgeRep ε) := by
      have := (Subgroup.mem_subgroupOf).mp (inv_mem hmem)
      simpa [hh₂] using this
    have := stabilizer_conj ch₂.τ
      ((h₂⁻¹ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) : Gal(L/K))
      (ch₂.τ⁻¹ • Γ.edgeRep ε) hs
    rwa [smul_inv_smul] at this
  · show ((Quotient.out (EdgeChoice.cosetCongr ch₁ ch₂ η) :
        ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) : Gal(L/K)) * ch₂.τ⁻¹ = _
    rw [hout]
    show ((Quotient.out η : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) : Gal(L/K))
        * (ch₁.τ⁻¹ * ch₂.τ) * ((h₂⁻¹ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) : Gal(L/K))
        * ch₂.τ⁻¹ = _
    show _ = ((Quotient.out η : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) : Gal(L/K)) * ch₁.τ⁻¹
        * (ch₂.τ * ((h₂⁻¹ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) : Gal(L/K)) * ch₂.τ⁻¹)
    group

theorem phiComp_eq_phiAt (M : Rep Γ) (ch : Γ.EdgeChoice ε)
    (η : EdgeChoice.CosetIndex Γ ch) (m : ↥(M.vertexFixed (Γ.vertexRep i))) :
    phiComp M ch η m
      = phiAt M ε (EdgeChoice.rep Γ ch η * ch.τ⁻¹) ch.σ ch.sourceVertex
          (ch.cosetTarget η) m := rfl

theorem phiAt_congr (M : Rep Γ) {g g' s : Gal(L/K)} (hgg : g = g')
    (hs : s • Γ.vertexRep i = Γ.toRQuiver.source (Γ.edgeRep ε))
    (hg : g • Γ.toRQuiver.target (Γ.edgeRep ε) = Γ.vertexRep j)
    (hg' : g' • Γ.toRQuiver.target (Γ.edgeRep ε) = Γ.vertexRep j)
    (m : ↥(M.vertexFixed (Γ.vertexRep i))) :
    phiAt M ε g s hs hg m = phiAt M ε g' s hs hg' m := by subst hgg; rfl

/-- **`phiComp` is independent of the §2.6 choice**, along `cosetCongr`. -/
theorem phiComp_choice_indep (M : Rep Γ) (ch₁ ch₂ : Γ.EdgeChoice ε)
    (η : EdgeChoice.CosetIndex Γ ch₁) (w : ↥(M.vertexFixed (Γ.vertexRep i))) :
    phiComp M ch₂ (EdgeChoice.cosetCongr ch₁ ch₂ η) w = phiComp M ch₁ η w := by
  obtain ⟨h, hh, hgeq⟩ := ch₁.rep_tau_congr ch₂ η
  have hgh : ((EdgeChoice.rep Γ ch₁ η * ch₁.τ⁻¹) * h) • Γ.toRQuiver.target (Γ.edgeRep ε)
      = Γ.vertexRep j := by rw [← hgeq]; exact ch₂.cosetTarget _
  rw [phiComp_eq_phiAt, phiComp_eq_phiAt,
    phiAt_congr M hgeq ch₂.sourceVertex (ch₂.cosetTarget _) hgh w,
    phiAt_stab M ε (EdgeChoice.rep Γ ch₁ η * ch₁.τ⁻¹) ch₂.σ ch₂.sourceVertex hh
      (ch₁.cosetTarget η) hgh w,
    phiAt_source_indep M ε (EdgeChoice.rep Γ ch₁ η * ch₁.τ⁻¹) ch₂.σ ch₁.σ
      ch₂.sourceVertex ch₁.sourceVertex (ch₁.cosetTarget η) w]

/-- …and so is the twist it multiplies by. -/
theorem twist_choice_indep (ch₁ ch₂ : Γ.EdgeChoice ε)
    (η : EdgeChoice.CosetIndex Γ ch₁) (c : ↥(Γ.edgeOrbitField ε)) :
    (EdgeChoice.rep Γ ch₂ (EdgeChoice.cosetCongr ch₁ ch₂ η) * ch₂.τ⁻¹) (c : L)
      = (EdgeChoice.rep Γ ch₁ η * ch₁.τ⁻¹) (c : L) := by
  obtain ⟨h, hh, hgeq⟩ := ch₁.rep_tau_congr ch₂ η
  rw [hgeq, AlgEquiv.mul_apply,
    show h (c : L) = (c : L) from (IntermediateField.mem_fixedField_iff _ _).mp c.2 _ hh]

open scoped Classical in
/-- **The edge descent does not depend on the §2.6 choice** — clause `RQ2-2.26-C1`'s `∀ ch`. -/
theorem edgeDescent_choice_indep (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch₁ ch₂ : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₁ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch₁)
    (e₂ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch₂)
    (f₁ f₂ : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j)))
    (h₁ : IsEdgeDescent M ch₁ e₁ f₁) (h₂ : IsEdgeDescent M ch₂ e₂ f₂) : f₁ = f₂ := by
  classical
  letI : Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
  letI : ∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch₁ ε)) :=
    fun ε => @Fintype.ofFinite _ (finite_cosetIndex (ch₁ ε))
  letI : ∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch₂ ε)) :=
    fun ε => @Fintype.ofFinite _ (finite_cosetIndex (ch₂ ε))
  have key : ∀ t : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i)),
      ((f₁ t : M.M (Γ.vertexRep j))) = ((f₂ t : M.M (Γ.vertexRep j))) := by
    intro t
    induction t using repTensor_induction with
    | h0 => rw [map_zero, map_zero]
    | hmk w m =>
        have hv1 := h₁.2 (phiTotal M ch₁) (phiTotal_single M ch₁) (Balanced.mk w m) 1
        have hv2 := h₂.2 (phiTotal M ch₂) (phiTotal_single M ch₂) (Balanced.mk w m) 1
        rw [phiTotal_e0_generator M ch₁ e₁ h₁.1 w m 1, one_smul] at hv1
        rw [phiTotal_e0_generator M ch₂ e₂ h₂.1 w m 1, one_smul] at hv2
        rw [← hv1, ← hv2]
        refine Finset.sum_congr rfl fun ε _ => ?_
        exact Fintype.sum_equiv (EdgeChoice.cosetCongr (ch₁ ε) (ch₂ ε)) _ _ (fun η => by
          rw [twist_choice_indep, phiComp_choice_indep])
    | hadd p q hp hq =>
        rw [map_add, map_add, Submodule.coe_add, Submodule.coe_add, hp, hq]
  exact LinearMap.ext fun t => Subtype.ext (key t)

end ChoiceIndep

end C2

open scoped Classical in
/-- **Proposition** (`unlabeled:3`, census `RQ2-2.24`).

`Φ_{ij}` — the map of clause `RQ2-2.24-H1`, defined on the right-hand side of `eq:WiiMjLpre` by

`(m_{ε,η} ⊗ a_{ε,η}) ↦ Σ_{ε,η} φ_{t(e_ε), η τ_ε^{-1}} φ_{e_ε} φ_{v_i, σ_ε}(m_{ε,η}) · a_{ε,η}`

— is `G_{v_j}`-**equivariant** for the rational structure `Θ_{ij}` (clause `RQ2-2.24-C1`) and
therefore, by `RQ2-2.23` and Galois descent, **descends** to a map
`f_{ij} : W_i ⊗_{L_i} {}_iM_j → W_j` (clause `RQ2-2.24-C2`) which is `L_j`-**linear**
(clause `RQ2-2.24-C3`).

@census    RQ2-2.24
@source    prop:phidescends
@clauses   RQ2-2.24-H1, RQ2-2.24-C1, RQ2-2.24-C2, RQ2-2.24-C3
@imports   none
@divergence JUSTIFIED_REFORMULATION on clauses `RQ2-2.24-H1` and `RQ2-2.24-C1`.

`H1` — `Φ_{ij}` is pinned by its value on the **single `(ε,η)`-components** rather than by the
displayed sum. The two are equivalent: `Φ_{ij}` is `L`-linear (its type), the components generate
`⊕_ε ∏_η —` because the outer index is a direct sum and the inner one finite (clause
`RQ2-2.23-C6`), and on a general element the displayed sum is what linearity then gives. Stating it
componentwise avoids putting a `Finset.sum` over a quotient type into a census-carrying signature
— and the sum's finiteness is *itself* one of the things `RQ2-2.23-C6` has to establish, so making
the statement depend on it would be circular. The composite is `phiComp`, which is the source's,
with `φ_{v_i,σ_ε}` for the source's printed `φ_{e_i,σ_ε}` exactly as the census note records.

`C1` — the equivariance is stated against the rational structure **as it acts on the pre-image
object**, i.e. against any `Θ'` satisfying the source's own `eq:explicitdecompositiontwisting`,
`(m_η ⊗ a_η) ↦ (m_{σ^{-1}η} ⊗ σ a_{σ^{-1}η})`. That is precisely the map the source's proof of this
proposition uses ("where we invoked `eq:explicitdecompositiontwisting` for the first identity"), and
`RQ2-2.23-C5` is what identifies it with `Θ_{ij}`. Quantifying over any such `Θ'` rather than
naming one keeps this row independent of `RQ2-2.23`'s existential witness.

`C2`/`C3` are one conjunct: the descended `f_{ij}` is *specified* by
`Φ (e₀ (t ⊗ a)) = a · ι(f t)` for a **named, existentially supplied** identification
`e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch` — `RQ2-2.20`'s identification — which says exactly
that `f_{ij} ⊗ 1_L` is `Φ_{ij}`; its type carries `C3`'s `L_j`-linearity, and the inclusion `ι` is
`W_j ⊆ M(v_j)`.  The pairing `(e₀, f)` is packaged as `IsEdgeDescent M ch e₀ f`, whose **first**
conjunct pins `e₀` by `RQ2-2.20-C1`'s generator formula, so the row asserts the descent along the
canonical identification and not merely along some isomorphism of that type.

> **Dated correction, 2026-09-02 (`WORKFLOW.md` §7 class 7 / R6; G4 finding `V-S5G4-2`).** This
> paragraph read "for every `RQ2-2.22`-style identification `e₀`", and was stale in three ways: the
> conjunct is `∃ e₀ f, IsEdgeDescent M ch e₀ f`, not a `∀` (the `V-S5b-16` quantifier repair,
> sanctioned and verified at G2, `VERIFICATION-S5b.md` §D.3/§F.1 — the inline comment on the
> conjunct below already recorded it); `e₀` is `RQ2-2.20`'s identification
> (`wiiMjL ≃ₗ wiiMjLpreRhs`), not `RQ2-2.22`'s (`wiiMjL ≃ₗ wiiMjLRhs`); and `IsEdgeDescent`'s
> generator pin (finding `S5-F8`, coordinator-sanctioned, `DESIGN-NOTES` §56/§58) was not
> mentioned.  For **this** row the `∃`-plus-pin form is *stronger* than the paragraph claimed;
> for the four rows that take `IsEdgeDescent → …` as a hypothesis the pin narrows the hypothesis,
> which is what makes `RQ2-2.25-C4` provable at all.  Corrected in place; no statement, proof or
> clause changes.

Proof plan (G4): `C1` is the source's four-line computation, whose only non-formal step is
`eq:explicitdecompositiontwisting`; `C2` is stage S0's `galoisDescent` applied to the
`L(v_j)`-rational structure `RQ2-2.23` provides — the descent whose *continuity* hypothesis is
exactly what clause `RQ2-2.23-C6` was added to supply.
-/
theorem phi_descends (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε) :
    ∃ Φ : wiiMjLpreRhs M ch →ₗ[L] M.M (Γ.vertexRep j),
      -- `H1`: the defining formula, componentwise
      (∀ (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)) (a : L)
          (m : ↥(M.vertexFixed (Γ.vertexRep i))),
        Φ (DirectSum.lof L _ _ ε (Pi.single η (Twist.ofL a ⊗ₜ m)))
          = a • phiComp M (ch ε) η m) ∧
      -- `C1`: `G_{v_j}`-equivariance, against `eq:explicitdecompositiontwisting`
      (∀ Θ' : ↥(stabilizer Gal(L/K) (Γ.vertexRep j)) →
            (wiiMjLpreRhs M ch ≃+ wiiMjLpreRhs M ch),
        (∀ (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) (ε : Γ.EdgeOrbit i j)
            (η : EdgeChoice.CosetIndex Γ (ch ε)) (a : L)
            (m : ↥(M.vertexFixed (Γ.vertexRep i))),
          Θ' σ (DirectSum.lof L _ _ ε (Pi.single η (Twist.ofL a ⊗ₜ m)))
            = DirectSum.lof L _ _ ε
                (Pi.single (σ • η) (Twist.ofL ((σ : Gal(L/K)) a) ⊗ₜ m))) →
        ∀ (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep j))) (x : wiiMjLpreRhs M ch),
          Φ (Θ' σ x) = M.φ' (σ : Gal(L/K)) σ.2 (Φ x)) ∧
      -- `C2` and `C3`: the descent, `L_j`-linear.  **`∃ e₀`, not `∀ e₀`** (finding `V-S5b-16`):
      -- the descent exists along the *canonical* identification, not along every one.  For an
      -- arbitrary `e₀` the composite `Φ ∘ e₀` need not land in `W_j`, and the verifier's compiled
      -- refutation forces `f = 0` whenever `G_{v_j} ≠ 1`.
      (∃ (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
        (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
              →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j))),
          IsEdgeDescent M ch e₀ f) := by
  classical
  letI : Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
  letI : ∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε)) :=
    fun ε => @Fintype.ofFinite _ (finite_cosetIndex (ch ε))
  obtain ⟨e₀, h₀⟩ := wiiMj_baseChange_pre M i j ch
  exact ⟨phiTotal M ch, phiTotal_single M ch, phiTotal_equivariant M ch,
    ⟨e₀, edgeDescentMap M ch e₀ h₀, isEdgeDescent_edgeDescentMap M ch e₀ h₀⟩⟩

/-! ### `RQ2-2.25` — `F` on morphisms  (G4)

All four clauses come from `ψ`'s own two axioms, `rational` (`eq:koecheractiononrephom`) and
`edge`, read through the transported `φ'`/`φEdge'`:

* `C1` is `rational` at `σ ∈ G_{v_i}` (`Rep.Hom.equivariant`);
* `C2` is the restriction of `ψ_{v_i}` to the invariants, well defined **by** `C1`
  (`Rep.Hom.vertexFixedMap`);
* `C3` is `rational` twice and `edge` once, in the order `phiComp` composes them (`phiComp_hom`);
* `C4` is `C3` summed: `RQ2-2.24`'s `Φ` evaluated on `RQ2-2.20-C1`'s generators is the double sum
  `∑_ε ∑_η (ητ_ε⁻¹)(m_ε) · φ_{ε,η}(w)`, and `ψ_{v_j}` — being `L`-linear — passes through it
  termwise (`F_map_C4`).

**`C4` is the clause finding `S5-F8` was about**, and it is provable here **only because the
repair landed**: `IsEdgeDescent`'s first conjunct now pins `eM`/`eN` to `RQ2-2.20-C1`'s
identification, which is what lets `phiTotal_e0_generator` evaluate them.  Before the repair the
clause was refutable (the entailment is compiled above), and no proof of it existed to be found.

@census none (G4 engine for `RQ2-2.25`)
-/

/-- `eq:koecheractiononrephom` for the transported `φ'`. -/
theorem Rep.Hom.rational' {M N : Rep Γ} (ψ : Rep.Hom M N) (σ : Gal(L/K)) {v w : Γ.V}
    (h : σ • v = w) (m : M.M v) :
    ψ.ψ w (M.φ' σ h m) = N.φ' σ h (ψ.ψ v m) := by
  rw [M.φ'_apply, N.φ'_apply, Rep.eqCast_natural ψ.ψ h, ψ.rational]

/-- `ψ` commutes with the transported edge maps. -/
theorem Rep.Hom.edge' {M N : Rep Γ} (ψ : Rep.Hom M N) (e : Γ.E) {a b : Γ.V}
    (ha : Γ.toRQuiver.source e = a) (hb : Γ.toRQuiver.target e = b) (m : M.M a) :
    ψ.ψ b (M.φEdge' e ha hb m) = N.φEdge' e ha hb (ψ.ψ a m) := by
  subst ha; subst hb; exact ψ.edge e m

/-- **Clause `RQ2-2.25-C1`**: `ψ_{v}` is `G_v`-equivariant. -/
theorem Rep.Hom.equivariant {M N : Rep Γ} (ψ : Rep.Hom M N) (v : Γ.V)
    (σ : ↥(stabilizer Gal(L/K) v)) (m : M.M v) :
    ψ.ψ v (M.φ' (σ : Gal(L/K)) σ.2 m) = N.φ' (σ : Gal(L/K)) σ.2 (ψ.ψ v m) :=
  ψ.rational' (σ : Gal(L/K)) σ.2 m

/-- **Clause `RQ2-2.25-C2`**: `ψ_v` restricts to the invariants. -/
noncomputable def Rep.Hom.vertexFixedMap {M N : Rep Γ} (ψ : Rep.Hom M N) (i : Γ.VertexOrbit) :
    ↥(M.vertexFixed (Γ.vertexRep i)) →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ]
      ↥(N.vertexFixed (Γ.vertexRep i)) where
  toFun m := ⟨ψ.ψ (Γ.vertexRep i) (m : M.M (Γ.vertexRep i)), fun σ => by
    rw [← ψ.equivariant (Γ.vertexRep i) σ, m.2 σ]⟩
  map_add' m m' := Subtype.ext (by
    show ψ.ψ (Γ.vertexRep i) ((m : M.M (Γ.vertexRep i)) + (m' : M.M (Γ.vertexRep i))) = _
    rw [map_add]
    rfl)
  map_smul' r m := Subtype.ext (by
    show ψ.ψ (Γ.vertexRep i)
        ((algebraMap (Γ.toSpecies.L i) L (MulOpposite.unop r)) • (m : M.M (Γ.vertexRep i)))
      = (algebraMap (Γ.toSpecies.L i) L (MulOpposite.unop r))
          • ψ.ψ (Γ.vertexRep i) (m : M.M (Γ.vertexRep i))
    rw [map_smul])

@[simp] theorem Rep.Hom.vertexFixedMap_coe {M N : Rep Γ} (ψ : Rep.Hom M N) (i : Γ.VertexOrbit)
    (m : ↥(M.vertexFixed (Γ.vertexRep i))) :
    ((ψ.vertexFixedMap i m : N.M (Γ.vertexRep i)))
      = ψ.ψ (Γ.vertexRep i) (m : M.M (Γ.vertexRep i)) := rfl

/-- **Clause `RQ2-2.25-C3`**: the `ψ_{v_i}` commute with the components of `Φ_{ij}`. -/
theorem phiComp_hom {M N : Rep Γ} (ψ : Rep.Hom M N) {i j : Γ.VertexOrbit}
    {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch)
    (m : ↥(M.vertexFixed (Γ.vertexRep i))) :
    phiComp N ch η (ψ.vertexFixedMap i m)
      = ψ.ψ (Γ.vertexRep j) (phiComp M ch η m) := by
  show N.φ' (EdgeChoice.rep Γ ch η * ch.τ⁻¹) (ch.cosetTarget η)
      (N.φEdge' (Γ.edgeRep ε) rfl rfl
        (N.φ' ch.σ ch.sourceVertex (ψ.ψ (Γ.vertexRep i) (m : M.M (Γ.vertexRep i))))) = _
  rw [← ψ.rational' ch.σ ch.sourceVertex (m : M.M (Γ.vertexRep i)),
    ← ψ.edge' (Γ.edgeRep ε) rfl rfl,
    ← ψ.rational' (EdgeChoice.rep Γ ch η * ch.τ⁻¹) (ch.cosetTarget η)]
  rfl

open scoped Classical in
/-- **Clause `RQ2-2.25-C4`**: `(ψ_i)` is a morphism of `K`-species representations. -/
theorem F_map_C4 {M N : Rep Γ} (ψ : Rep.Hom M N) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (eM : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (eN : wiiMjL N i j ≃ₗ[L] wiiMjLpreRhs N ch)
    (fM : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j)))
    (fN : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(N.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(N.vertexFixed (Γ.vertexRep j)))
    (hM : IsEdgeDescent M ch eM fM) (hN : IsEdgeDescent N ch eN fN)
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) :
    fN (Balanced.mk (ψ.vertexFixedMap i w) m)
      = ψ.vertexFixedMap j (fM (Balanced.mk w m)) := by
  classical
  letI : Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
  letI : ∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε)) :=
    fun ε => @Fintype.ofFinite _ (finite_cosetIndex (ch ε))
  have hMval := hM.2 (phiTotal M ch) (phiTotal_single M ch) (Balanced.mk w m) 1
  have hNval := hN.2 (phiTotal N ch) (phiTotal_single N ch)
    (Balanced.mk (ψ.vertexFixedMap i w) m) 1
  rw [phiTotal_e0_generator M ch eM hM.1 w m 1, one_smul] at hMval
  rw [phiTotal_e0_generator N ch eN hN.1 (ψ.vertexFixedMap i w) m 1, one_smul] at hNval
  refine Subtype.ext ?_
  rw [← hNval]
  show _ = ψ.ψ (Γ.vertexRep j) ((fM (Balanced.mk w m) : M.M (Γ.vertexRep j)))
  rw [← hMval, map_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [map_smul, phiComp_hom]

/-! ### `RQ2-2.25` — `F` on morphisms -/

/-- **Proposition** (`unlabeled:4`, census `RQ2-2.25`).

For any morphism `ψ : M_K → N_K` in `Rep(Γ_K)` and any `i ∈ I` (clause `RQ2-2.25-H1`):

* `ψ_{v_i}` is `G_{v_i}`-**equivariant** — clause `RQ2-2.25-C1`, which is
  `eq:koecheractiononrephom` (`Rep.Hom.rational`) restricted to the stabilizer;
* hence it **descends** to a canonical `L_i`-**linear** `ψ_i : M(v_i)^{G_{v_i}} → N(v_i)^{G_{v_i}}`
  — clause `RQ2-2.25-C2`, the `ψ'` below, pinned by the fact that it is `ψ_{v_i}` on elements;
* the `ψ_{v_i}` **commute with the `Φ_{ij}`** — clause `RQ2-2.25-C3`, stated on `phiComp`, the
  `(ε,η)`-component of `Φ_{ij}`;
* and the collection `(ψ_i)_{i ∈ I}` defines a **morphism** `S(M_K) → S(N_K)` of `K`-species
  representations — clause `RQ2-2.25-C4`, the commuting square of `RQ2-2.17-C5` for the descended
  structure maps.

@census    RQ2-2.25
@source    prop:fonmorphisms
@clauses   RQ2-2.25-H1, RQ2-2.25-C1, RQ2-2.25-C2, RQ2-2.25-C3, RQ2-2.25-C4
@imports   none
@divergence JUSTIFIED_REFORMULATION on clauses `RQ2-2.25-C3` and `RQ2-2.25-C4`.

`C3` — "the `ψ_{v_i}` commute with the `Φ_{ij}`" is stated on `phiComp`, the `(ε,η)`-component,
for the reason `RQ2-2.24`'s `@divergence` gives: `Φ_{ij}` itself is pinned componentwise, so the
componentwise square is the same statement and it does not import the finiteness `RQ2-2.23-C6` is
still establishing.

`C4` — "defines a morphism of `K`-species representations" is stated as the commuting square of
clause `RQ2-2.17-C5` on pure tensors, `f^N_{ij}(ψ_i w ⊗ m) = ψ_j(f^M_{ij}(w ⊗ m))`, quantified over
any descents `f^M`, `f^N` in the sense of `IsEdgeDescent`. It is **not** stated as a
`Species.Rep.Hom` between `F(M_K)` and `F(N_K)`, because `F` is `RQ2-2.26` and does not exist yet:
stating it that way would make this row depend on the next one, which is the wrong direction — the
source derives `RQ2-2.26` *from* here. `Species.Rep.Hom.comm_mk` shows the pure-tensor square is
equivalent to the bundled one, so nothing is lost, and `RQ2-2.26` assembles the morphism from
exactly this datum.

Proof plan (G4): `C1` is `Rep.Hom.rational` at `σ ∈ G_{v_i}`; `C2` is the restriction of `ψ_{v_i}`
to invariants, well defined by `C1`; `C3` is `Rep.Hom.edge` together with `Rep.Hom.rational`,
which is the source's "elementary calculation … by `eq:koecheractiononrep`"; `C4` follows from `C3`
by Galois descent, the maps on both sides being descents of maps that already agree.
-/
theorem F_map (M N : Rep Γ) (ψ : Rep.Hom M N) :
    -- `C1`: `G_{v_i}`-equivariance of `ψ_{v_i}`
    (∀ (i : Γ.VertexOrbit) (σ : ↥(stabilizer Gal(L/K) (Γ.vertexRep i)))
        (m : M.M (Γ.vertexRep i)),
      ψ.ψ (Γ.vertexRep i) (M.φ' (σ : Gal(L/K)) σ.2 m)
        = N.φ' (σ : Gal(L/K)) σ.2 (ψ.ψ (Γ.vertexRep i) m)) ∧
    -- `C2`: the descended, `L_i`-linear `ψ_i`
    ∃ ψ' : ∀ i : Γ.VertexOrbit,
        ↥(M.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥(N.vertexFixed (Γ.vertexRep i)),
      (∀ (i : Γ.VertexOrbit) (m : ↥(M.vertexFixed (Γ.vertexRep i))),
        ((ψ' i m : N.M (Γ.vertexRep i)))
          = ψ.ψ (Γ.vertexRep i) (m : M.M (Γ.vertexRep i))) ∧
      -- `C3`: the `ψ_{v_i}` commute with the `Φ_{ij}`
      (∀ (i j : Γ.VertexOrbit) (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
          (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε))
          (m : ↥(M.vertexFixed (Γ.vertexRep i))),
        phiComp N (ch ε) η (ψ' i m)
          = ψ.ψ (Γ.vertexRep j) (phiComp M (ch ε) η m)) ∧
      -- `C4`: `(ψ_i)` is a morphism of `K`-species representations
      (∀ (i j : Γ.VertexOrbit) (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
          (eM : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
          (eN : wiiMjL N i j ≃ₗ[L] wiiMjLpreRhs N ch)
          (fM : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
                →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j)))
          (fN : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(N.vertexFixed (Γ.vertexRep i))
                →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(N.vertexFixed (Γ.vertexRep j))),
        IsEdgeDescent M ch eM fM → IsEdgeDescent N ch eN fN →
        ∀ (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j),
          fN (Balanced.mk (ψ' i w) m) = ψ' j (fM (Balanced.mk w m))) :=
  ⟨fun i σ m => ψ.equivariant (Γ.vertexRep i) σ m,
    ψ.vertexFixedMap, fun _ _ => rfl,
    fun _ _ ch ε η m => phiComp_hom ψ (ch ε) η m,
    fun _ _ ch eM eN fM fN hM hN w m => F_map_C4 ψ ch eM eN fM fN hM hN w m⟩

/-! ### The canonical descent, and `RQ2-2.26-H2`  (G4)

`RQ2-2.24` proves `∃ e₀ f, IsEdgeDescent`; `edgeDescent_unique` and `edgeDescent_choice_indep` say
that `f` is determined — by nothing at all, once the pin is in `IsEdgeDescent`.  So the choice
below is a choice of *name*, not of object: `edgeDescentOf_eq` says every descent, for every §2.6
choice, **is** it.  That is clause `RQ2-2.26-C1`'s content, ahead of `F` itself.

`vertexDescentBalanced` is clause `RQ2-2.26-H2` (`eq:WitoMvi`): `Balanced.equivTensor` turns
`W_i ⊗_{L_i} L` into mathlib's `L ⊗_{L_i} W_i`, the `S5-F7` bridges upgrade `≃ₗ[Lᵐᵒᵖ]` to `≃ₗ[L]`
(the `outerEquivL` pattern, at a different carrier), and `vertexDescentEquiv` — stage S0's descent
at `L/L(v_i)` — lands it on `M(v_i)`.

@census none (G4 engine for `RQ2-2.26`)
-/

open scoped Classical in
/-- The canonical descent `f_{ij}`, taken at the G5 choice `EdgeChoice.choose`. -/
noncomputable def edgeDescentOf (M : Rep Γ) (i j : Γ.VertexOrbit) :
    EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
      →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j)) :=
  ((phi_descends M (fun ε : Γ.EdgeOrbit i j =>
    EdgeChoice.choose Γ ε)).choose_spec.2.2.choose_spec).choose

open scoped Classical in
theorem isEdgeDescent_edgeDescentOf (M : Rep Γ) (i j : Γ.VertexOrbit) :
    IsEdgeDescent M (fun ε : Γ.EdgeOrbit i j => EdgeChoice.choose Γ ε)
      (phi_descends M (fun ε : Γ.EdgeOrbit i j => EdgeChoice.choose Γ ε)).choose_spec.2.2.choose
      (edgeDescentOf M i j) :=
  ((phi_descends M (fun ε : Γ.EdgeOrbit i j =>
    EdgeChoice.choose Γ ε)).choose_spec.2.2.choose_spec).choose_spec

/-- **Clause `RQ2-2.26-C1`'s content**: every descent, for every choice, is `edgeDescentOf`. -/
theorem edgeDescentOf_eq (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j)))
    (h : IsEdgeDescent M ch e₀ f) : edgeDescentOf M i j = f :=
  edgeDescent_choice_indep M _ ch _ e₀ _ f (isEdgeDescent_edgeDescentOf M i j) h

/-- `L ⊗_{L_i} W_i`: the `L`- and `Lᵐᵒᵖ`-actions agree, by one `mul_comm`. -/
theorem tensor_smul_L_eq_op_W (M : Rep Γ) (i : Γ.VertexOrbit) (c : L)
    (z : L ⊗[Γ.toSpecies.L i] ↥(M.vertexFixed (Γ.vertexRep i))) :
    c • z = MulOpposite.op c • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
      show (c • a) ⊗ₜ[Γ.toSpecies.L i] t = (MulOpposite.op c • a) ⊗ₜ _
      congr 1
      show c * a = a * c
      exact mul_comm c a
  | add p q hp hq => rw [smul_add, smul_add, hp, hq]

/-- **Clause `RQ2-2.26-H2`** (`eq:WitoMvi`): Galois descent identifies `W_i ⊗_{L_i} L` with
`M(v_i)`. -/
noncomputable def vertexDescentBalanced (M : Rep Γ) (i : Γ.VertexOrbit) :
    Balanced K (Γ.toSpecies.L i) L L ↥(M.vertexFixed (Γ.vertexRep i))
      ≃ₗ[L] M.M (Γ.vertexRep i) :=
  (AddEquiv.toLinearEquiv
      (Balanced.equivTensor (K := K) (A := Γ.toSpecies.L i) (B := L)
        (X := ↥(M.vertexFixed (Γ.vertexRep i))) (fun _ _ => rfl)).toAddEquiv
      (fun c x => by
        exact (congrArg (Balanced.equivTensor (K := K) (A := Γ.toSpecies.L i) (B := L)
              (X := ↥(M.vertexFixed (Γ.vertexRep i))) (fun _ _ => rfl)).toAddEquiv
            (balanced_smul_L_eq_op (Γ.toSpecies.L i)
              ↥(M.vertexFixed (Γ.vertexRep i)) c x)).trans
          (((Balanced.equivTensor (K := K) (A := Γ.toSpecies.L i) (B := L)
              (X := ↥(M.vertexFixed (Γ.vertexRep i))) (fun _ _ => rfl)).map_smul
            (MulOpposite.op c) x).trans
            (tensor_smul_L_eq_op_W M i c _).symm))).trans
    (vertexDescentEquiv M (Γ.vertexRep i))

end RationalQuiver

end RationalQuivers
