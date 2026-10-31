module

public import RationalQuivers.Quiver.BaseChange

@[expose] public section

/-!
# Restriction of `K`-rational quivers

Formalizes Definition `def:quiverrestriction` of §1.2 of `latex/rational_quivers.tex`
(census `RQ2-1.06`).

## Main definitions / results
* `RationalQuivers.InducedSet` — the induced set `G ×_H X` along a group homomorphism `H →* G`;
  this is the functor `Gal(L/K) ×_{Gal(L/E')} (−)` the source applies to `V`, `E`, `s` and `t`.
* `RationalQuivers.RationalQuiver.restrictionObj` — Definition `def:quiverrestriction` on objects
  (census `RQ2-1.06`).
* `RationalQuivers.RationalQuiver.restriction` — the same as a functor
  `{E'-rational quivers} ⥤ {K-rational quivers}`, the left adjoint of `RQ2-1.07`.
* `RationalQuivers.InducedSet.mk_eq_mk_iff`, `.mk_ne_mk_of_notMem_range`, `.card_eq` and
  `RationalQuiver.card_restrictionObj_V`/`_E` — the **separation and counting** API of `G ×_H X`
  (G5): two classes are equal only up to `H`, and `|G ×_H X| = [G : im f] · |X|`, so
  `|res_{E'/K} Γ|_V = [E' : K] · |V|`.

## Implementation notes

The source writes `Gal(L/K) ×_{Gal(L/E)} V` with `Gal(L/E)` regarded as a subgroup of `Gal(L/K)`.
We realise the inclusion as the group homomorphism `galRestrict` of `Quiver/BaseChange.lean`, so
`InducedSet` is stated for an arbitrary homomorphism `f : H →* G`; that costs nothing and keeps the
construction independent of the field theory. Finiteness of the induced sets and continuity of the
induced action are exactly where the source's hypothesis "`E'/K` finite" (clause `RQ2-1.06-H2`) is
consumed, through `finiteIndex_range_galRestrict` and `isOpenMap_galRestrict`.
-/

universe u

namespace RationalQuivers

open CategoryTheory

/-! ### The induced set `G ×_H X` -/

section Induced

variable {H G : Type u} [Group G] [Group H]

/-- The equivalence relation on `G × X` defining `G ×_H X`: `(g h, x) ∼ (g, h • x)`, written here
as `(g, x) ∼ (g * f h⁻¹, h • x)`.

@census none (helper for `RQ2-1.06`)
-/
def inducedSetoid (f : H →* G) (X : Type u) [MulAction H X] : Setoid (G × X) where
  r p q := ∃ h : H, q = (p.1 * f h⁻¹, h • p.2)
  iseqv :=
    { refl := fun p => ⟨1, by simp⟩
      symm := by
        rintro ⟨a, x⟩ ⟨b, y⟩ ⟨h, hh⟩
        rw [Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        exact ⟨h⁻¹, by simp [mul_assoc]⟩
      trans := by
        rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
        rw [Prod.mk.injEq] at h₁' h₂'
        obtain ⟨rfl, rfl⟩ := h₁'
        obtain ⟨rfl, rfl⟩ := h₂'
        exact ⟨h₂ * h₁, by simp [mul_assoc, mul_smul]⟩ }

/-- The induced set `G ×_H X` along a group homomorphism `f : H →* G`. For `H = Gal(L/E')`,
`G = Gal(L/K)` and `f = galRestrict` this is the functor
`Gal(L/K) ×_{Gal(L/E')} (−) : {finite Gal(L/E')-sets} → {finite Gal(L/K)-sets}`
that `def:quiverrestriction` applies to `V`, `E`, `s` and `t`, and whose universal property the
proof of `prop:quiverrestrictionbasechangeadjunction` invokes.

@census none (helper for `RQ2-1.06`, `RQ2-1.07`)
-/
def InducedSet (f : H →* G) (X : Type u) [MulAction H X] : Type u :=
  Quotient (inducedSetoid f X)

namespace InducedSet

variable (f : H →* G) {X Y : Type u} [MulAction H X] [MulAction H Y]

/-- The class of `(g, x)` in `G ×_H X`.

@census none (helper)
-/
def mk (g : G) (x : X) : InducedSet f X := Quotient.mk (inducedSetoid f X) (g, x)

/-- The defining relation of `G ×_H X`. Not a `simp` lemma: `h` occurs on the right but not on the
left, so it can never fire; it is used with explicit arguments. @census none (helper) -/
theorem mk_smul (g : G) (h : H) (x : X) : mk f g x = mk f (g * f h⁻¹) (h • x) :=
  Quotient.sound (s := inducedSetoid f X) ⟨h, rfl⟩

/-- **The defining relation, as an iff.** `mk f g x = mk f g' x'` exactly when the two
representatives differ by an element of `H`.  Without this lemma nothing in the tree can prove two
classes of `G ×_H X` *distinct*, so nothing distinguishes `InducedSet f X` from `X` — which is what
the G5 probe for `RQ2-1.06`/`RQ2-1.07` (`restrictionObj` genuinely enlarges `V`) needs.

@census none (helper for `RQ2-1.06`; separation of classes)
-/
theorem mk_eq_mk_iff (g g' : G) (x x' : X) :
    mk f g x = mk f g' x' ↔ ∃ h : H, g' = g * f h⁻¹ ∧ x' = h • x := by
  constructor
  · intro hq
    obtain ⟨h, hh⟩ := Quotient.exact hq
    rw [Prod.mk.injEq] at hh
    exact ⟨h, hh.1, hh.2⟩
  · rintro ⟨h, rfl, rfl⟩
    exact mk_smul f g h x

/-- Two classes whose `G`-components lie in **different cosets** of `im f` are distinct, whatever
their `X`-components.  The practical form of `mk_eq_mk_iff` for non-degeneracy arguments: for
`f = galRestrict` and `E' ≠ K` the cosets are the `[E' : K] > 1` classes of `Gal(L/E')`.

@census none (helper for `RQ2-1.06`; separation of classes)
-/
theorem mk_ne_mk_of_notMem_range {g g' : G} (hg : g⁻¹ * g' ∉ f.range) (x x' : X) :
    mk f g x ≠ mk f g' x' := by
  intro hq
  obtain ⟨h, hg', -⟩ := (mk_eq_mk_iff f g g' x x').mp hq
  exact hg ⟨h⁻¹, by rw [hg']; group⟩

/-- For injective `f`, `X` embeds into `G ×_H X` through any fixed `g` — in particular `G ×_H X`
is at least as big as `X`.  `galRestrict` is injective (`injective_galRestrict`).

@census none (helper for `RQ2-1.06`)
-/
theorem mk_left_injective (hf : Function.Injective f) (g : G) :
    Function.Injective (fun x : X => mk f g x) := by
  intro x x' hx
  obtain ⟨h, hg, rfl⟩ := (mk_eq_mk_iff f g g x x').mp hx
  have hfh : f h⁻¹ = 1 := mul_eq_left.mp hg.symm
  have h1 : h⁻¹ = 1 := hf (by rw [hfh, map_one])
  rw [inv_eq_one.mp h1, one_smul]

/-- Left translation of `G ×_H X` by `g ∈ G`.

@census none (helper)
-/
def translate (g : G) : InducedSet f X → InducedSet f X :=
  Quotient.map (fun p => (g * p.1, p.2)) (by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨h, hh⟩
    rw [Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    exact ⟨h, by simp [mul_assoc]⟩)

/-- Translation on representatives. @census none (helper) -/
@[simp]
theorem translate_mk (g g' : G) (x : X) : translate f g (mk f g' x) = mk f (g * g') x := rfl

/-- The `G`-action on `G ×_H X` by left translation, as a permutation representation.

@census none (helper: supplies the rational structure of `RQ2-1.06`)
-/
def permHom (X : Type u) [MulAction H X] : G →* Equiv.Perm (InducedSet f X) where
  toFun g :=
    { toFun := translate f g
      invFun := translate f g⁻¹
      left_inv := by
        refine Quotient.ind ?_
        rintro ⟨a, x⟩
        exact congrArg (Quotient.mk (inducedSetoid f X)) (by simp)
      right_inv := by
        refine Quotient.ind ?_
        rintro ⟨a, x⟩
        exact congrArg (Quotient.mk (inducedSetoid f X)) (by simp) }
  map_one' := by
    refine Equiv.ext ?_
    refine Quotient.ind ?_
    rintro ⟨a, x⟩
    exact congrArg (Quotient.mk (inducedSetoid f X)) (by simp)
  map_mul' g g' := by
    refine Equiv.ext ?_
    refine Quotient.ind ?_
    rintro ⟨a, x⟩
    exact congrArg (Quotient.mk (inducedSetoid f X)) (by simp [mul_assoc])

/-- The `G`-action on representatives. @census none (helper) -/
@[simp]
theorem permHom_apply (g : G) (g' : G) (x : X) :
    permHom f X g (mk f g' x) = mk f (g * g') x := rfl

/-- Functoriality of `G ×_H (−)` in the `H`-set: an `H`-equivariant map `X → Y` induces a
`G`-equivariant map `G ×_H X → G ×_H Y`. This is what `def:quiverrestriction` means by
`Gal(L/K) ×_{Gal(L/E')} s` and `Gal(L/K) ×_{Gal(L/E')} t`.

@census none (helper: clauses RQ2-1.06-C3, RQ2-1.06-C4)
-/
def map (φ : X → Y) (hφ : ∀ (h : H) (x : X), φ (h • x) = h • φ x) :
    InducedSet f X → InducedSet f Y :=
  Quotient.map (fun p => (p.1, φ p.2)) (by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨h, hh⟩
    rw [Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    exact ⟨h, by simp [hφ]⟩)

/-- The induced map on representatives. @census none (helper) -/
@[simp]
theorem map_mk (φ : X → Y) (hφ : ∀ (h : H) (x : X), φ (h • x) = h • φ x) (g : G) (x : X) :
    map f φ hφ (mk f g x) = mk f g (φ x) := rfl

/-- The induced map is `G`-equivariant; this is the `Gal(L/K)`-equivariance
`eq:stgaloisequivariance` of the restricted quiver.

@census none (helper: clause RQ2-1.06-C5)
-/
theorem map_permHom (φ : X → Y) (hφ : ∀ (h : H) (x : X), φ (h • x) = h • φ x)
    (g : G) (q : InducedSet f X) :
    map f φ hφ (permHom f X g q) = permHom f Y g (map f φ hφ q) := by
  refine Quotient.inductionOn q ?_
  rintro ⟨a, x⟩
  rfl

/-- `G ×_H X` is finite when `X` is finite and `f` has finite-index image. For
`f = galRestrict` and `E'/K` finite the index is `[E' : K]`
(`finiteIndex_range_galRestrict`), so the restricted quiver again has finite vertex and edge sets
(clauses `RQ2-1.01-H1`, `RQ2-1.01-H2` for `RQ2-1.06`).

@census none (helper: clause RQ2-1.06-C5)
-/
theorem mkOut_surjective (X : Type u) [MulAction H X] :
    Function.Surjective (fun p : (G ⧸ f.range) × X => mk f (Quotient.out p.1) p.2) := by
  refine Quotient.ind ?_
  rintro ⟨g, x⟩
  obtain ⟨h, hh⟩ :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk (s := f.range) g))
  have hg : g * f h⁻¹ = Quotient.out (QuotientGroup.mk (s := f.range) g) := by
    rw [map_inv, hh]; group
  refine ⟨(QuotientGroup.mk (s := f.range) g, h • x), ?_⟩
  show mk f (Quotient.out (QuotientGroup.mk (s := f.range) g)) (h • x) = mk f g x
  rw [mk_smul f g h, hg]

theorem finite (X : Type u) [MulAction H X] [Finite X] (hf : f.range.FiniteIndex) :
    Finite (InducedSet f X) := by
  haveI := hf
  exact Finite.of_surjective _ (mkOut_surjective f X)

/-- For injective `f` the surjection of `mkOut_surjective` is a **bijection**: every class has
exactly one representative whose `G`-component is the chosen representative of its coset.

@census none (helper for `RQ2-1.06`; the counting lemma below)
-/
theorem mkOut_bijective (hf : Function.Injective f) (X : Type u) [MulAction H X] :
    Function.Bijective (fun p : (G ⧸ f.range) × X => mk f (Quotient.out p.1) p.2) := by
  refine ⟨?_, mkOut_surjective f X⟩
  rintro ⟨c₁, x₁⟩ ⟨c₂, x₂⟩ hq
  obtain ⟨h, hg, rfl⟩ := (mk_eq_mk_iff f _ _ x₁ x₂).mp hq
  have hmem : (Quotient.out c₁)⁻¹ * Quotient.out c₂ ∈ f.range :=
    ⟨h⁻¹, by rw [hg]; group⟩
  have hc : c₁ = c₂ := by
    rw [← QuotientGroup.out_eq' c₁, ← QuotientGroup.out_eq' c₂]
    exact QuotientGroup.eq.mpr hmem
  subst hc
  have hfh : f h⁻¹ = 1 := mul_eq_left.mp hg.symm
  have h1 : h⁻¹ = 1 := hf (by rw [hfh, map_one])
  simp [inv_eq_one.mp h1]

/-- **The counting formula** `|G ×_H X| = [G : im f] · |X|`, for injective `f`.  This is what makes
`res_{E'/K}` a genuine *induction*: the restricted quiver is `[E' : K]` times bigger, not a
relabelling of `X`.

@census none (helper for `RQ2-1.06`; non-degeneracy of restriction)
-/
theorem card_eq (hf : Function.Injective f) (X : Type u) [MulAction H X] :
    Nat.card (InducedSet f X) = f.range.index * Nat.card X := by
  rw [← Nat.card_eq_of_bijective _ (mkOut_bijective f hf X), Nat.card_prod,
    Subgroup.index_eq_card]

/-- The translation action on `G ×_H X` is smooth (continuous for the discrete topology) as soon
as the action on `X` is smooth and `f` is an open map. For `f = galRestrict` and `E'/K` finite this
is `isOpenMap_galRestrict`, and it is clause `RQ2-1.06-C5`: `res_{E'/K} Γ_{E'}` is again a
`K`-rational quiver.

@census none (helper: clause RQ2-1.06-C5)
-/
theorem isSmooth [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H]
    (X : Type u) [MulAction H X]
    (aX : H →* Equiv.Perm X) (haX : ∀ (h : H) (x : X), aX h x = h • x)
    (hX : IsSmooth aX) (hopen : IsOpenMap f) :
    IsSmooth (permHom f X) := by
  refine Quotient.ind ?_
  rintro ⟨a, x⟩
  have hstab : IsOpen {h : H | h • x = x} := by
    have h0 := hX x
    simpa only [haX] using h0
  have hconj : IsOpenMap (fun y : G => a * y * a⁻¹) :=
    ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight a⁻¹)).isOpenMap
  have hset : {g : G | (permHom f X) g (mk f a x) = mk f a x}
      = (fun y : G => a * y * a⁻¹) '' (f '' {h : H | h • x = x}) := by
    ext g
    constructor
    · intro hg
      obtain ⟨h, hh⟩ := Quotient.exact hg
      rw [Prod.mk.injEq] at hh
      obtain ⟨h1, h2⟩ := hh
      refine ⟨f h, ⟨h, h2.symm, rfl⟩, ?_⟩
      rw [map_inv, eq_comm, mul_inv_eq_iff_eq_mul] at h1
      show a * f h * a⁻¹ = g
      rw [← h1]
      group
    · rintro ⟨y, ⟨h, hh, rfl⟩, rfl⟩
      show mk f (a * f h * a⁻¹ * a) x = mk f a x
      rw [inv_mul_cancel_right]
      refine Quotient.sound (s := inducedSetoid f X) ⟨h, ?_⟩
      rw [Prod.mk.injEq]
      exact ⟨by rw [map_inv, mul_inv_cancel_right], hh.symm⟩
  show IsOpen {g : G | (permHom f X) g (mk f a x) = mk f a x}
  rw [hset]
  exact hconj _ (hopen _ hstab)

end InducedSet

end Induced

/-! ### Restriction of rational quivers -/

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
variable (E' : IntermediateField K L) [FiniteDimensional K E']

namespace RationalQuiver

/-- The underlying classical quiver of `res_{E'/K} Γ_{E'}`: the four induced sets
`Gal(L/K) ×_{Gal(L/E')} V`, `Gal(L/K) ×_{Gal(L/E')} E`, `Gal(L/K) ×_{Gal(L/E')} s`,
`Gal(L/K) ×_{Gal(L/E')} t` of `def:quiverrestriction`.

@census none (helper: clauses RQ2-1.06-C1 … C4)
-/
def restrictionRQuiver (Γ : RationalQuiver (E' : Type u) L) : RQuiver.{u} where
  V := InducedSet (galRestrict K L E') Γ.V
  E := InducedSet (galRestrict K L E') Γ.E
  source := InducedSet.map _ Γ.toRQuiver.source (fun σ e => Γ.source_smul σ e)
  target := InducedSet.map _ Γ.toRQuiver.target (fun σ e => Γ.target_smul σ e)
  finite_V := InducedSet.finite _ Γ.V (finiteIndex_range_galRestrict K L E')
  finite_E := InducedSet.finite _ Γ.E (finiteIndex_range_galRestrict K L E')

/-- **Definition 1.6** (`def:quiverrestriction`), on objects.
For any intermediate field `L/E'/K` with `E'/K` finite and any `E'`-rational quiver
`Γ_{E'} = (Γ, ρ)` with `Γ = (V,E,s,t)`, the *restriction* of `Γ_{E'}` to `K` is

`res_{E'/K} Γ_{E'} = (Gal(L/K) ×_{Gal(L/E')} V, Gal(L/K) ×_{Gal(L/E')} E,`
`  Gal(L/K) ×_{Gal(L/E')} s, Gal(L/K) ×_{Gal(L/E')} t)`.

Since `E'/K` is finite, `Gal(L/E')` is an open subgroup of `Gal(L/K)`, so the induced actions of
`Gal(L/K)` on the two induced sets are again continuous and `res_{E'/K} Γ_{E'}` is indeed a
`K`-rational quiver.

@census    RQ2-1.06
@source    def:quiverrestriction
@clauses   RQ2-1.06-Hs1, RQ2-1.06-H1, RQ2-1.06-H2, RQ2-1.06-C1, RQ2-1.06-C2, RQ2-1.06-C3, RQ2-1.06-C4, RQ2-1.06-C5
@imports   none
@divergence none. Clauses `RQ2-1.06-H1` and `RQ2-1.06-H2` are the arguments
`E' : IntermediateField K L`, `[FiniteDimensional K E']` and `Γ : RationalQuiver E' L`; clauses
`RQ2-1.06-C1`–`C4` are the four fields of `restrictionRQuiver`; clause `RQ2-1.06-C5` is the *type*
`RationalQuiver K L`, whose smoothness fields are discharged by `InducedSet.isSmooth` from
`isOpenMap_galRestrict`, which is where the finiteness of `E'/K` is consumed. The source's
`E` for the intermediate field is written `E'` (ATTESTATION AN-11).
-/
def restrictionObj (Γ : RationalQuiver (E' : Type u) L) : RationalQuiver K L :=
  RationalQuiver.ofAction K L (restrictionRQuiver K L E' Γ)
    (InducedSet.permHom (galRestrict K L E') Γ.V)
    (InducedSet.permHom (galRestrict K L E') Γ.E)
    (fun σ e => InducedSet.map_permHom (galRestrict K L E') Γ.toRQuiver.source
      (fun τ x => Γ.source_smul τ x) σ e)
    (fun σ e => InducedSet.map_permHom (galRestrict K L E') Γ.toRQuiver.target
      (fun τ x => Γ.target_smul τ x) σ e)
    (InducedSet.isSmooth _ Γ.V ((RQuiver.Aut.toPermV Γ.toRQuiver).comp Γ.ρ)
      (fun _ _ => rfl) Γ.smooth_V (isOpenMap_galRestrict K L E'))
    (InducedSet.isSmooth _ Γ.E ((RQuiver.Aut.toPermE Γ.toRQuiver).comp Γ.ρ)
      (fun _ _ => rfl) Γ.smooth_E (isOpenMap_galRestrict K L E'))

/-- **The restricted quiver's vertex count**: `|res_{E'/K} Γ|_V = [E' : K] · |V|`.  Combining
`InducedSet.card_eq` with `injective_galRestrict`, `range_galRestrict` and mathlib's
`IntermediateField.finrank_eq_fixingSubgroup_index`.  For `E' ≠ K` the factor is `> 1`, so
restriction is not the identity in disguise (the G5 non-degeneracy probe for `RQ2-1.06`/`RQ2-1.07`).

@census none (helper: non-degeneracy of `RQ2-1.06`)
-/
theorem card_restrictionObj_V (Γ : RationalQuiver (E' : Type u) L) :
    Nat.card (restrictionObj K L E' Γ).V = Module.finrank K E' * Nat.card Γ.V := by
  show Nat.card (InducedSet (galRestrict K L E') Γ.V) = _
  rw [InducedSet.card_eq _ (injective_galRestrict K L E'), range_galRestrict,
    ← IntermediateField.finrank_eq_fixingSubgroup_index L E']

/-- **P5 (adjunction non-degeneracy, `RQ2-1.06`/`RQ2-1.07`).** Restriction along `E'/K` **strictly**
enlarges the vertex set whenever `E' ≠ K`, so the induced-set construction is not the identity in
disguise.

`card_restrictionObj_V` above gives the *equation* `|res_{E'/K} Γ|_V = [E' : K] · |V|`; this
probe turns it into the *inequality* that is what non-degeneracy actually asserts, and names the
two side conditions that make it bite — a non-empty vertex set and a proper extension. Without
both, the equation is compatible with restriction doing nothing at all (`[E' : K] = 1`, or
`V = ∅`).

**Relocated from `Meta/Vacuity.lean` §3.2, 2026-09-05 (`G3(instrument, commission 7)`,
`workflow/ledger/OBLIGATIONS.md` C-M1-1 "Owed to the instrument owner" item 5) — verbatim, beside
its own content dependency `card_restrictionObj_V`, exactly as the ledger row asked.

@census none (G5.2 non-degeneracy witness for `RQ2-1.06`/`RQ2-1.07`, probe P5)
-/
theorem restrictionObj_strictly_enlarges (Γ : RationalQuiver (E' : Type u) L)
    (hV : 0 < Nat.card Γ.V) (hE' : 1 < Module.finrank K E') :
    Nat.card Γ.V < Nat.card (restrictionObj K L E' Γ).V := by
  rw [card_restrictionObj_V]
  exact lt_mul_of_one_lt_left hV hE'

/-- **The restricted quiver's edge count**: `|res_{E'/K} Γ|_E = [E' : K] · |E|`.

@census none (helper: non-degeneracy of `RQ2-1.06`)
-/
theorem card_restrictionObj_E (Γ : RationalQuiver (E' : Type u) L) :
    Nat.card (restrictionObj K L E' Γ).E = Module.finrank K E' * Nat.card Γ.E := by
  show Nat.card (InducedSet (galRestrict K L E') Γ.E) = _
  rw [InducedSet.card_eq _ (injective_galRestrict K L E'), range_galRestrict,
    ← IntermediateField.finrank_eq_fixingSubgroup_index L E']

/-- **Definition 1.6** (`def:quiverrestriction`) as a functor. The source calls restriction and
base change "adjoint pairs of functors" (Introduction), and
`prop:quiverrestrictionbasechangeadjunction` (`RQ2-1.07`) needs the action on morphisms.

@census none (helper: functorial form of `RQ2-1.06`, needed for `RQ2-1.07`)
-/
def restriction : RationalQuiver (E' : Type u) L ⥤ RationalQuiver K L where
  obj Γ := restrictionObj K L E' Γ
  map {Γ Γ'} φ :=
    { toRQuiverHom :=
        { onV := InducedSet.map _ φ.toRQuiverHom.onV φ.equivariant_V
          onE := InducedSet.map _ φ.toRQuiverHom.onE φ.equivariant_E
          onV_source := by
            refine Quotient.ind ?_
            rintro ⟨a, e⟩
            exact congrArg (Quotient.mk _) (by simp [φ.toRQuiverHom.onV_source e])
          onV_target := by
            refine Quotient.ind ?_
            rintro ⟨a, e⟩
            exact congrArg (Quotient.mk _) (by simp [φ.toRQuiverHom.onV_target e]) }
      equivariant_V := by
        refine fun σ => Quotient.ind ?_
        rintro ⟨a, v⟩
        rfl
      equivariant_E := by
        refine fun σ => Quotient.ind ?_
        rintro ⟨a, e⟩
        rfl }
  map_id Γ := by
    refine Hom.ext ?_
    refine RQuiver.Hom.ext ?_ ?_ <;> funext q <;>
      refine Quotient.inductionOn q ?_ <;> rintro ⟨a, x⟩ <;> rfl
  map_comp φ ψ := by
    refine Hom.ext ?_
    refine RQuiver.Hom.ext ?_ ?_ <;> funext q <;>
      refine Quotient.inductionOn q ?_ <;> rintro ⟨a, x⟩ <;> rfl

end RationalQuiver

end RationalQuivers
