import RationalQuivers.Species.Orbits
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The `K`-rational quiver `Γ_K(S)` associated to an étale `K`-species

Formalizes the second half of §2.3 of `latex/rational_quivers.tex` (census `RQ2-2.12`). Stage **S4**.

## Main definitions / results
* `RationalQuivers.EtaleSpecies.structLeft`, `.structRight` — the canonical structure embeddings
  `τ_ε : L_i → L_ε` and `σ_ε : L_j → L_ε` (clause `RQ2-2.12-C5`).
* `RationalQuivers.EtaleSpecies.edgeSource`, `.edgeTarget` — `s(τ) = τ ∘ τ_ε` (`eq:tauespilon`) and
  `t(τ) = τ ∘ σ_ε` (`eq:sigmaespilon`), clauses `RQ2-2.12-C6`, `RQ2-2.12-C7`, and their
  `Gal(L/K)`-equivariance (clause `RQ2-2.12-C8`).
* `RationalQuivers.EtaleSpecies.prod_decomposition` — `{}_iM_j = ∏_ε L_ε` (clause `RQ2-2.12-C2`).
* `RationalQuivers.EtaleSpecies.etaleBialgebra_decomposition` —
  `eq:etalebialgebradecomposition` (clause `RQ2-2.12-C3`).
* `RationalQuivers.EtaleSpecies.toRationalQuiver` — `Γ_K(S)` (census `RQ2-2.12`).

## Implementation notes

**`s` and `t` are equivariance-free by construction.** The action on `E` and on `V` is
postcomposition with `σ`, and `s`, `t` are *pre*composition with the structure maps, so
`s(σ • τ) = σ • s(τ)` holds by `rfl`. Clause `RQ2-2.12-C8` is therefore recorded as two `rfl`
lemmas rather than as an assumption.

**Continuity.** `Γ_K(S)` is built over the splitting field `L`, which the §2.3 standing hypothesis
takes **finite** over `K`; `Gal(L/K)` is then discrete and the continuity clauses of
`def:rationalquivers` (`RQ2-1.02-C2`, `C3`) are vacuous — `RationalQuivers.IsSmooth.of_discreteTopology`.
This is exactly the source's "we may assume that `L/K` is finite and Galois".

**`eq:etalebialgebradecomposition` needs an embedding `L_j → L`.** The source writes
`{}_iM_j ⊗_{L_j} L`, which presupposes an `L_j`-algebra structure on `L`; over a general splitting
field there is no *canonical* one — `Hom_K(L_j,L)` is a torsor under `Gal(L/K)` (that is
`RQ2-2.10` itself). We therefore quantify the statement over the embedding `ι : L_j → L`, which is
the honest reading of the source's implicit choice, and index the product exactly as the source
does: `τ` runs through `Hom_{L_j}(L_ε, L)` — rendered as the `K`-embeddings `τ` of `L_ε` with
`τ ∘ σ_ε = ι` — while the left `L_i`-structure on the `(ε,τ)`-component is through
`σ = τ ∘ τ_ε` (`RQ2-2.12-C3`, as disambiguated by the r5 source edit, census AN-13).
-/

universe u

namespace RationalQuivers

open MulAction

open scoped TensorProduct

namespace EtaleSpecies

variable {K : Type u} [Field K] (S : EtaleSpecies.{u} K) (L : Type u) [Field L] [Algebra K L]

/-! ### The structure embeddings `τ_ε`, `σ_ε` -/

/-- **Clause `RQ2-2.12-C5`.** The canonical embedding `τ_ε : L_i → L_ε = {}_iM_j/ε`, i.e. the left
structure map of `{}_iM_j` followed by the residue map.

@census none (clause witness for `RQ2-2.12-C5`)
-/
noncomputable def structLeft (c : S.edgeIndexSet) : S.L c.1.1 →ₐ[K] S.residueField c :=
  (S.residueMap c).comp (S.left c.1.1 c.1.2)

/-- **Clause `RQ2-2.12-C5`.** The canonical embedding `σ_ε : L_j → L_ε`.

@census none (clause witness for `RQ2-2.12-C5`)
-/
noncomputable def structRight (c : S.edgeIndexSet) : S.L c.1.2 →ₐ[K] S.residueField c :=
  (S.residueMap c).comp (S.right c.1.1 c.1.2)

/-! ### `s` and `t` -/

/-- **Clause `RQ2-2.12-C6`** (`eq:tauespilon`). `s(τ) := τ ∘ τ_ε ∈ Hom_K(L_i,L) ⊆ V`.

@census none (clause witness for `RQ2-2.12-C6`)
-/
noncomputable def edgeSource (e : S.edgeSet L) : S.vertexSet L := ⟨e.1.1.1, e.2.comp (S.structLeft e.1)⟩

/-- **Clause `RQ2-2.12-C7`** (`eq:sigmaespilon`). `t(τ) := τ ∘ σ_ε ∈ Hom_K(L_j,L) ⊆ V`.

@census none (clause witness for `RQ2-2.12-C7`)
-/
noncomputable def edgeTarget (e : S.edgeSet L) : S.vertexSet L := ⟨e.1.1.2, e.2.comp (S.structRight e.1)⟩

/-- **Clause `RQ2-2.12-C8`**, source half: `s` is `Gal(L/K)`-equivariant. Both actions are
postcomposition with `σ` and `s` is precomposition with `τ_ε`, so this is `rfl`.

@census none (clause witness for `RQ2-2.12-C8`)
-/
@[simp] theorem edgeSource_smul (σ : Gal(L/K)) (e : S.edgeSet L) :
    S.edgeSource L (σ • e) = σ • S.edgeSource L e := rfl

/-- **Clause `RQ2-2.12-C8`**, target half: `t` is `Gal(L/K)`-equivariant.

@census none (clause witness for `RQ2-2.12-C8`)
-/
@[simp] theorem edgeTarget_smul (σ : Gal(L/K)) (e : S.edgeSet L) :
    S.edgeTarget L (σ • e) = σ • S.edgeTarget L e := rfl

/-! ### Finiteness of `V` and `E` -/

instance isArtinianRing_M (i j : S.I) : IsArtinianRing (S.M i j) :=
  IsArtinianRing.of_finite K (S.M i j)

instance finite_edgeIndexSet : Finite S.edgeIndexSet :=
  inferInstanceAs (Finite (Σ p : S.I × S.I, MaximalSpectrum (S.M p.1 p.2)))

instance finite_vertexSet : Finite (S.vertexSet L) :=
  inferInstanceAs (Finite (Σ i : S.I, (S.L i →ₐ[K] L)))

instance finite_edgeSet : Finite (S.edgeSet L) := by
  haveI : ∀ c : S.edgeIndexSet, Finite (S.residueField c →ₐ[K] L) := fun c => inferInstance
  exact inferInstanceAs (Finite (Σ c : S.edgeIndexSet, (S.residueField c →ₐ[K] L)))

/-! ### Maximal ideals of a finite product of fields

`{}_iM_j` is, by `prod_decomposition`, a finite product of fields, and `Γ_K(S)`'s edge set is
indexed by its maximal ideals. The three lemmas below identify those: a `K`-algebra map from a
finite product of fields into a **domain** factors through exactly one projection, so every maximal
ideal of the product is the kernel of a projection. They are stated for an arbitrary index type and
an arbitrary domain because that is the generality in which they are used (once for `Specm`, once
for the embeddings `{}_iM_j → L` of clause `RQ2-2.13-C4`), and they are the finite-product half of
what `RQ2-2.12-C2` provides.

@census none (helpers for clauses `RQ2-2.12-C2`, `RQ2-2.13-C4`)
-/

section PiFields

variable {K : Type u} [Field K] {ι : Type u} [Finite ι] {F : ι → Type u}
  [∀ e, Field (F e)] [∀ e, Algebra K (F e)] {B : Type u} [CommRing B] [IsDomain B] [Algebra K B]

/-- A `K`-algebra map from a finite product of fields into a field factors through exactly one
projection: the idempotents `Pi.single e 1` go to orthogonal idempotents of `B` summing to `1`, so
exactly one of them goes to `1`. -/
theorem exists_pi_index (g : (∀ e, F e) →ₐ[K] B) [DecidableEq ι] :
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


theorem exists_pi_factor (g : (∀ e, F e) →ₐ[K] B) :
    ∃ (e₀ : ι) (ĝ : F e₀ →ₐ[K] B), g = ĝ.comp (Pi.evalAlgHom K F e₀) := by
  classical
  obtain ⟨e₀, hone, hdep⟩ := exists_pi_index g
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
        rw [hdep (Pi.single e₀ (algebraMap K (F e₀) k)) (algebraMap K (∀ e, F e) k) (by simp)]
        exact g.commutes k }, ?_⟩
  refine AlgHom.ext fun x => ?_
  exact (hdep (Pi.single e₀ (x e₀)) x (by simp)).symm

theorem maximalSpectrum_pi (m : MaximalSpectrum (∀ e, F e)) :
    ∃ e₀ : ι, m.asIdeal = RingHom.ker (Pi.evalAlgHom K F e₀) := by
  haveI : (m.asIdeal).IsPrime := m.isMaximal.isPrime
  haveI : IsDomain ((∀ e, F e) ⧸ m.asIdeal) := inferInstance
  obtain ⟨e₀, ĝ, hg⟩ := exists_pi_factor (K := K) (Ideal.Quotient.mkₐ K m.asIdeal)
  refine ⟨e₀, ?_⟩
  have hker : RingHom.ker (Ideal.Quotient.mkₐ K m.asIdeal) = m.asIdeal := Ideal.mk_ker
  rw [← hker, hg]
  ext x
  simp only [RingHom.mem_ker, AlgHom.comp_apply]
  constructor
  · intro hx
    have hinj : Function.Injective ĝ := fun a b hab => ĝ.toRingHom.injective hab
    exact (map_eq_zero_iff ĝ hinj).mp hx
  · intro hx
    rw [show ((Pi.evalAlgHom K F e₀) x) = 0 from hx, map_zero]

end PiFields


/-! ### Splitting a finite algebra after base change to a splitting field

`eq:etalebialgebradecomposition` says that `L ⊗_{L_j} {}_iM_j` is a product of copies of `L`, one
for each pair `(ε, τ)`. The mechanism is general and is isolated here: for an `F`-algebra `A` and a
field `B ⊇ F`, every `F`-algebra map `φ : A → B` gives an evaluation `B ⊗_F A → B`, and the
resulting map into the product over a family of such `φ` is

* **surjective** whenever the family is injective — the kernels are then distinct maximal ideals
  (an `L`-algebra map to `L` with a given kernel is determined by it), hence pairwise coprime, and
  the Chinese remainder theorem (`Ideal.exists_forall_sub_mem_ideal`) produces a preimage;
* **injective** as soon as the index set has the right size, by `finrank_baseChange` and
  `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`.

No `Fintype` structure on the index is used beyond its cardinality, and no choice of basis.
-/

section TensorSplit

variable {F A B : Type u} [Field F] [CommRing A] [Algebra F A] [Field B] [Algebra F B]

/-- Evaluation of `B ⊗_F A` at an `F`-algebra map `φ : A → B`: `a ⊗ x ↦ a · φ x`. -/
noncomputable def tensorEval (φ : A →ₐ[F] B) : (B ⊗[F] A) →ₐ[B] B :=
  Algebra.TensorProduct.lift (AlgHom.id B B) φ (fun _ _ => Commute.all _ _)

theorem tensorEval_tmul (φ : A →ₐ[F] B) (a : B) (x : A) :
    tensorEval φ (a ⊗ₜ[F] x) = a * φ x := by
  simp [tensorEval]

theorem tensorEval_surjective (φ : A →ₐ[F] B) : Function.Surjective (tensorEval φ) :=
  fun b => ⟨b ⊗ₜ[F] 1, by rw [tensorEval_tmul, map_one, mul_one]⟩

theorem eq_of_tensorEval_ker_eq {φ ψ : A →ₐ[F] B}
    (h : RingHom.ker (tensorEval φ) = RingHom.ker (tensorEval ψ)) : φ = ψ := by
  have key : ∀ z, tensorEval ψ z = tensorEval φ z := by
    intro z
    have hz : z - algebraMap B (B ⊗[F] A) (tensorEval φ z) ∈ RingHom.ker (tensorEval φ) := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
      simp
    rw [h, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at hz
    exact hz
  refine AlgHom.ext fun x => ?_
  have hx := key (1 ⊗ₜ[F] x)
  rw [tensorEval_tmul, tensorEval_tmul, one_mul, one_mul] at hx
  exact hx.symm

/-- The canonical `B`-algebra map `B ⊗_F A → (P → B)` attached to a family of `F`-algebra maps. -/
noncomputable def tensorPi {P : Type u} (g : P → (A →ₐ[F] B)) : (B ⊗[F] A) →ₐ[B] (P → B) :=
  Pi.algHom B _ (fun p => tensorEval (g p))

theorem tensorPi_apply {P : Type u} (g : P → (A →ₐ[F] B)) (z : B ⊗[F] A) (p : P) :
    tensorPi g z p = tensorEval (g p) z := rfl

theorem tensorPi_surjective {P : Type u} [Finite P] {g : P → (A →ₐ[F] B)}
    (hg : Function.Injective g) : Function.Surjective (tensorPi g) := by
  intro y
  have hmax : ∀ p, (RingHom.ker (tensorEval (g p))).IsMaximal :=
    fun p => RingHom.ker_isMaximal_of_surjective _ (tensorEval_surjective (g p))
  have hcop : Pairwise (Function.onFun IsCoprime (fun p => RingHom.ker (tensorEval (g p)))) := by
    intro p q hpq
    refine Ideal.isCoprime_iff_sup_eq.mpr ((hmax p).coprime_of_ne (hmax q) ?_)
    intro hk
    exact hpq (hg (eq_of_tensorEval_ker_eq hk))
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal hcop
    (fun p => algebraMap B (B ⊗[F] A) (y p))
  refine ⟨r, funext fun p => ?_⟩
  have h := hr p
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at h
  exact h

theorem tensorPi_bijective {P : Type u} [Finite P] [Module.Finite F A]
    {g : P → (A →ₐ[F] B)} (hg : Function.Injective g)
    (hcard : Nat.card P = Module.finrank F A) :
    Function.Bijective (tensorPi g) := by
  classical
  haveI := Fintype.ofFinite P
  haveI : Module.Finite B (B ⊗[F] A) := inferInstance
  have hrank : Module.finrank B (B ⊗[F] A) = Module.finrank B (P → B) := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card,
      ← Nat.card_eq_fintype_card, hcard]
  refine ⟨?_, tensorPi_surjective hg⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (tensorPi g).toLinearMap)
    hrank).mpr (tensorPi_surjective hg)

end TensorSplit

/-! ### The two decompositions of `{}_iM_j` -/

/-- **Clause `RQ2-2.12-C2`.** `{}_iM_j = ∏_{ε ∈ Specm {}_iM_j} L_ε`, with `L_ε = {}_iM_j/ε` the
residue field at `ε`.

Proof plan (G4): `{}_iM_j` is a finite étale, hence reduced, Artinian `K`-algebra, so
`IsArtinianRing.equivPi` gives the canonical decomposition into the residue fields at its (finitely
many) maximal ideals; it is an isomorphism of `{}_iM_j`-algebras, in particular of `K`-algebras.
Reducedness comes from `Algebra.Etale.iff_exists_algEquiv_prod` (a finite product of fields).

@census none (clause witness for `RQ2-2.12-C2`)
-/
theorem prod_decomposition (i j : S.I) :
    Nonempty (S.M i j ≃ₐ[K] ∀ ε : MaximalSpectrum (S.M i j), S.M i j ⧸ ε.asIdeal) := by
  haveI : IsArtinianRing (S.M i j) := IsArtinianRing.of_finite K (S.M i j)
  haveI : IsReduced (S.M i j) := Algebra.FormallyUnramified.isReduced_of_field K (S.M i j)
  exact ⟨(IsArtinianRing.equivPi (S.M i j)).restrictScalars K⟩

/-- The bundled residue field `L_ε` **is** the ambient quotient `{}_iM_j/ε`, on the nose: the
bundle's `Field` is `Ideal.Quotient.field` on the same `CommRing` and its `Algebra K` is the same
composite, so the identity map is a `K`-algebra equivalence. -/
noncomputable def quotientEquivResidueField (c : S.edgeIndexSet) :
    (S.M c.1.1 c.1.2 ⧸ c.2.asIdeal) ≃ₐ[K] S.residueField c where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl
  map_add' := fun _ _ => rfl
  commutes' := fun _ => rfl

/-- Every residue field of an edge algebra is a **separable** extension of `K`: `{}_iM_j` is
formally étale, the decomposition `prod_decomposition` transports that to the product of the
residue fields, and `FormallyEtale.pi_iff` to each factor. -/
theorem isSeparable_residueField (c : S.edgeIndexSet) :
    Algebra.IsSeparable K (S.residueField c) := by
  obtain ⟨e⟩ := S.prod_decomposition c.1.1 c.1.2
  haveI h1 : Algebra.FormallyEtale K (∀ ε : MaximalSpectrum (S.M c.1.1 c.1.2),
      S.M c.1.1 c.1.2 ⧸ ε.asIdeal) :=
    (Algebra.FormallyEtale.iff_of_equiv e).mp inferInstance
  haveI h2 : Algebra.FormallyEtale K (S.M c.1.1 c.1.2 ⧸ c.2.asIdeal) :=
    (Algebra.FormallyEtale.pi_iff _).mp h1 c.2
  haveI h3 : Algebra.FormallyEtale K (S.residueField c) :=
    (Algebra.FormallyEtale.iff_of_equiv (S.quotientEquivResidueField c)).mp h2
  exact (Algebra.FormallyUnramified.iff_isSeparable K (S.residueField c)).mp inferInstance

/-- `dim_K {}_iM_j = Σ_ε dim_K L_ε`. -/
theorem finrank_M_eq_sum (i j : S.I) [Fintype (MaximalSpectrum (S.M i j))] :
    Module.finrank K (S.M i j)
      = ∑ ε : MaximalSpectrum (S.M i j),
          Module.finrank K (S.residueField ⟨(i, j), ε⟩) := by
  classical
  obtain ⟨e⟩ := S.prod_decomposition i j
  have h1 : Module.finrank K (S.M i j)
      = Module.finrank K (∀ ε : MaximalSpectrum (S.M i j), S.M i j ⧸ ε.asIdeal) :=
    e.toLinearEquiv.finrank_eq
  rw [h1, Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl fun ε _ =>
    ((S.quotientEquivResidueField ⟨(i, j), ε⟩).toLinearEquiv).finrank_eq


/-- The `K`-embeddings `τ : L_ε → L` that restrict along `σ_ε` to a *given* embedding
`ι : L_j → L` — the source's `Hom_{L_j}(L_ε, L)` once the `L_j`-structure of `L` is fixed by `ι`
(see the module header).

@census none (clause witness for `RQ2-2.12-C3`)
-/
def embOver (c : S.edgeIndexSet) (ι : S.L c.1.2 →ₐ[K] L) : Type u :=
  {τ : S.residueField c →ₐ[K] L // τ.comp (S.structRight c) = ι}

/-- Counting the embeddings over a fixed `ι`: `[L_j : K] · #Hom_{L_j}(L_ε, L) = [L_ε : K]`.
The middle term is `[L_ε : L_j]` by `AlgHom.natCard_of_splits`, `L` splitting `L_ε` over `L_j`
because it splits it over `K` and `minpoly L_j x ∣ minpoly K x`. -/
theorem finrank_mul_card_embOver (hL : S.IsSplitBy L)
    (c : S.edgeIndexSet) (ι : S.L c.1.2 →ₐ[K] L) :
    Module.finrank K (S.L c.1.2) * Nat.card (S.embOver L c ι)
      = Module.finrank K (S.residueField c) := by
  classical
  haveI := hL.galois
  haveI := hL.findim
  letI : Algebra (S.L c.1.2) L := ι.toAlgebra
  letI : Algebra (S.L c.1.2) (S.residueField c) := (S.structRight c).toAlgebra
  haveI ht1 : IsScalarTower K (S.L c.1.2) L :=
    IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  haveI ht2 : IsScalarTower K (S.L c.1.2) (S.residueField c) :=
    IsScalarTower.of_algebraMap_eq fun x => ((S.structRight c).commutes x).symm
  haveI : Module.Finite (S.L c.1.2) (S.residueField c) :=
    Module.Finite.of_restrictScalars_finite K (S.L c.1.2) (S.residueField c)
  haveI : Algebra.IsSeparable K (S.residueField c) := S.isSeparable_residueField c
  haveI : Algebra.IsSeparable (S.L c.1.2) (S.residueField c) :=
    Algebra.isSeparable_tower_top_of_isSeparable K (S.L c.1.2) (S.residueField c)
  have hsplit : ∀ x : S.residueField c,
      (Polynomial.map (algebraMap (S.L c.1.2) L) (minpoly (S.L c.1.2) x)).Splits := by
    intro x
    have hdvd : minpoly (S.L c.1.2) x ∣ Polynomial.map (algebraMap K (S.L c.1.2)) (minpoly K x) :=
      minpoly.dvd_map_of_isScalarTower K (S.L c.1.2) x
    have hmap : Polynomial.map (algebraMap (S.L c.1.2) L)
          (Polynomial.map (algebraMap K (S.L c.1.2)) (minpoly K x))
        = Polynomial.map (algebraMap K L) (minpoly K x) := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    have hsp : (Polynomial.map (algebraMap K L) (minpoly K x)).Splits :=
      S.splits_minpoly_residueField L hL c x
    rw [← hmap] at hsp
    refine hsp.of_dvd ?_ (Polynomial.map_dvd _ hdvd)
    rw [hmap]
    exact Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x))
  have hcard : Nat.card (S.embOver L c ι) = Nat.card (S.residueField c →ₐ[S.L c.1.2] L) :=
    Nat.card_congr
      { toFun := fun τ => ⟨τ.1.toRingHom, fun b =>
          congrArg (fun f : S.L c.1.2 →ₐ[K] L => f b) τ.2⟩
        invFun := fun σ => ⟨σ.restrictScalars K, AlgHom.ext fun b => σ.commutes b⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hcard, AlgHom.natCard_of_splits (S.L c.1.2) (S.residueField c) L hsplit]
  exact Module.finrank_mul_finrank K (S.L c.1.2) (S.residueField c)



/-- **Clause `RQ2-2.12-C3`** (`eq:etalebialgebradecomposition`).
Fix an embedding `ι : L_j → L` and regard `L` as an `L_j`-algebra through it. Then
`L ⊗_{L_j} {}_iM_j` decomposes canonically as an `L_i,L`-bialgebra into the product, over **all**
pairs `(ε, τ)` with `ε ∈ Specm {}_iM_j` and `τ ∈ Hom_{L_j}(L_ε,L)`, of copies of `L` — the source's
`⊕_{ε ∈ Specm {}_iM_j} ∏_τ L_ε ⊗_{σ,L_ε,τ} L`, each summand `L_ε ⊗_{σ,L_ε,τ} L` being `L` — and on
the `(ε,τ)`-component the left `L_i`-structure is given through `σ = τ ∘ τ_ε ∈ Hom_K(L_i,L)`, which
is the second conjunct.

**Corrected under verification finding F-2 (2026-08-30).** The statement previously fixed a single
`ε` (it quantified over `c : edgeIndexSet`, which carries one maximal ideal, and indexed the
right-hand side by the `τ`'s over that `ε` alone) while the left-hand side was the whole edge
algebra. That is not merely weaker but **false** as soon as `Specm {}_iM_j` has more than one point:
the two sides then have different `L`-dimensions. The regression witness is in this module —
`twoEdge`, an étale `ℝ`-species with a two-point `Specm`, together with
`twoEdge_no_single_block_equiv`. The `ι`-quantification, which the verifier examined separately and
accepted as strictly stronger than the source's implicit single choice, is unchanged.

Proof plan (G4): `prod_decomposition` splits `{}_iM_j` into its residue fields; each `L_ε` is
finite over `K` and split by `L` (`hL.splits_M`), so `L ⊗_{L_j} L_ε ≅ ∏_τ L` with `τ` running over
the `L_j`-embeddings — the standard "a separable algebra splits after base change to a splitting
field" computation — and the products assemble over `ε`. The left-`L_i` bookkeeping is read off
componentwise.

@census none (clause witness for `RQ2-2.12-C3`)
-/
theorem etaleBialgebra_decomposition (hL : S.IsSplitBy L) (i j : S.I) (ι : S.L j →ₐ[K] L) :
    letI : Algebra (S.L j) L := ι.toAlgebra
    letI : Algebra (S.L j) (S.M i j) := (S.right i j).toAlgebra
    ∃ f : (L ⊗[S.L j] S.M i j) ≃ₐ[L]
        ((p : Σ ε : MaximalSpectrum (S.M i j), S.embOver L ⟨(i, j), ε⟩ ι) → L),
      ∀ (α : S.L i) (m : S.M i j)
        (p : Σ ε : MaximalSpectrum (S.M i j), S.embOver L ⟨(i, j), ε⟩ ι),
        f ((1 : L) ⊗ₜ[S.L j] (S.left i j α * m)) p
          = (p.2.1 (S.structLeft ⟨(i, j), p.1⟩ α)) * f ((1 : L) ⊗ₜ[S.L j] m) p := by
  classical
  haveI := hL.galois
  haveI := hL.findim
  letI : Algebra (S.L j) L := ι.toAlgebra
  letI : Algebra (S.L j) (S.M i j) := (S.right i j).toAlgebra
  haveI ht1 : IsScalarTower K (S.L j) L :=
    IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  haveI ht2 : IsScalarTower K (S.L j) (S.M i j) :=
    IsScalarTower.of_algebraMap_eq fun x => ((S.right i j).commutes x).symm
  haveI : Module.Finite (S.L j) (S.M i j) :=
    Module.Finite.of_restrictScalars_finite K (S.L j) (S.M i j)
  haveI : Fintype (MaximalSpectrum (S.M i j)) := Fintype.ofFinite _
  haveI hfin : ∀ ε : MaximalSpectrum (S.M i j), Finite (S.embOver L ⟨(i, j), ε⟩ ι) :=
    fun _ => Subtype.finite
  -- the family of `L_j`-algebra maps `{}_iM_j → L`, one for each pair `(ε, τ)`
  refine ⟨AlgEquiv.ofBijective (tensorPi
    (fun p : Σ ε : MaximalSpectrum (S.M i j), S.embOver L ⟨(i, j), ε⟩ ι =>
      (⟨(p.2.1.comp (S.residueMap ⟨(i, j), p.1⟩)).toRingHom, fun b =>
        congrArg (fun f : S.L j →ₐ[K] L => f b) p.2.2⟩ : S.M i j →ₐ[S.L j] L))) ?_, ?_⟩
  · -- bijectivity
    refine tensorPi_bijective ?_ ?_
    · -- injectivity of the family
      have hker : ∀ (ε : MaximalSpectrum (S.M i j))
          (τ : S.residueField (⟨(i, j), ε⟩ : S.edgeIndexSet) →ₐ[K] L) (x : S.M i j),
          τ (S.residueMap (⟨(i, j), ε⟩ : S.edgeIndexSet) x) = 0 ↔ x ∈ ε.asIdeal := by
        intro ε τ x
        have hinj : Function.Injective τ :=
          (τ : S.residueField (⟨(i, j), ε⟩ : S.edgeIndexSet) →+* L).injective
        constructor
        · intro h
          exact Ideal.Quotient.eq_zero_iff_mem.mp (hinj (h.trans (map_zero τ).symm))
        · intro h
          have h0 : S.residueMap (⟨(i, j), ε⟩ : S.edgeIndexSet) x = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr h
          exact (congrArg τ h0).trans (map_zero τ)
      rintro ⟨ε, τ, hτ⟩ ⟨ε', τ', hτ'⟩ h
      have hval : ∀ x : S.M i j, τ (S.residueMap ⟨(i, j), ε⟩ x)
          = τ' (S.residueMap ⟨(i, j), ε'⟩ x) := fun x =>
        congrArg (fun f : S.M i j →ₐ[S.L j] L => f x) h
      have hidx : ε = ε' := by
        refine MaximalSpectrum.ext (Ideal.ext fun x => ?_)
        rw [← hker ε τ x, ← hker ε' τ' x, hval x]
      subst hidx
      have hττ : τ = τ' := by
        refine AlgHom.ext fun y => ?_
        obtain ⟨x, rfl⟩ := S.residueMap_surjective (⟨(i, j), ε⟩ : S.edgeIndexSet) y
        exact hval x
      subst hττ
      rfl
    · -- the count
      have h1 : Nat.card (Σ ε : MaximalSpectrum (S.M i j), S.embOver L ⟨(i, j), ε⟩ ι)
          = ∑ ε : MaximalSpectrum (S.M i j), Nat.card (S.embOver L ⟨(i, j), ε⟩ ι) :=
        Nat.card_sigma
      have h2 : Module.finrank K (S.L j)
            * Nat.card (Σ ε : MaximalSpectrum (S.M i j), S.embOver L ⟨(i, j), ε⟩ ι)
          = Module.finrank K (S.M i j) := by
        rw [h1, Finset.mul_sum, S.finrank_M_eq_sum i j]
        exact Finset.sum_congr rfl fun ε _ => S.finrank_mul_card_embOver L hL ⟨(i, j), ε⟩ ι
      have h3 : Module.finrank K (S.L j) * Module.finrank (S.L j) (S.M i j)
          = Module.finrank K (S.M i j) :=
        Module.finrank_mul_finrank K (S.L j) (S.M i j)
      exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos (h2.trans h3.symm)
  · -- the `L_i`-structure formula
    intro α m p
    show tensorEval _ ((1 : L) ⊗ₜ[S.L j] (S.left i j α * m)) = _
    rw [tensorEval_tmul, one_mul]
    show (p.2.1 (S.residueMap ⟨(i, j), p.1⟩ (S.left i j α * m))) = _
    rw [map_mul, map_mul]
    show _ = p.2.1 (S.structLeft ⟨(i, j), p.1⟩ α) * tensorEval _ ((1 : L) ⊗ₜ[S.L j] m)
    rw [tensorEval_tmul, one_mul]
    rfl


/-! ### Regression witness for verification finding **F-2**

The smallest étale species whose edge algebra has a **multi-point** `Specm`, in the exact shape the
verifier used to refute the previous statement of `etaleBialgebra_decomposition`. Its absence is
what let that defect through, so it stays here permanently, in the pattern stage S3 set with the
`literal_baseChange_*` counterexamples of finding S3-F2.
-/

/-- `ℂ/ℝ` is étale. -/
noncomputable instance etaleComplexReal : Algebra.Etale ℝ ℂ :=
  ⟨Algebra.FormallyEtale.of_isSeparable ℝ ℂ,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- An étale `ℝ`-species with **one** vertex `L_⋆ = ℂ` and edge algebra `{}_⋆M_⋆ = ℂ × ℂ`, whose
`Specm` therefore has **two** points. Every hypothesis of `etaleBialgebra_decomposition` holds for
it (`twoEdge_isSplitBy`), so it is a witness inside that statement's own domain.

@census none (regression witness for verification finding F-2)
-/
noncomputable def twoEdge : EtaleSpecies.{0} ℝ where
  I := Unit
  L := fun _ => ℂ
  M := fun _ _ => (Fin 2 → ℂ)
  left := fun _ _ => Pi.algHom ℝ _ fun _ => AlgHom.id ℝ ℂ
  right := fun _ _ => Pi.algHom ℝ _ fun _ => AlgHom.id ℝ ℂ

/-- `twoEdge` is split by `ℂ`: `ℂ/ℝ` is finite Galois and `ℂ` is algebraically closed.

@census none (regression witness for verification finding F-2)
-/
theorem twoEdge_isSplitBy : twoEdge.IsSplitBy ℂ := by
  haveI := RationalQuivers.isGalois_real_complex
  exact { splits_L := fun _ _ => IsAlgClosed.splits _
          splits_M := fun _ _ _ => IsAlgClosed.splits _ }

/-- The left-hand side of `eq:etalebialgebradecomposition` for `twoEdge` has `ℂ`-dimension **2**.

@census none (regression witness for verification finding F-2)
-/
theorem twoEdge_finrank_lhs : Module.finrank ℂ (ℂ ⊗[ℂ] (Fin 2 → ℂ)) = 2 := by
  have h : Module.finrank ℂ (ℂ ⊗[ℂ] (Fin 2 → ℂ)) = Module.finrank ℂ (Fin 2 → ℂ) :=
    (Algebra.TensorProduct.lid ℂ (Fin 2 → ℂ)).toLinearEquiv.finrank_eq
  rw [h]
  simp

/-- **The refutation.** No `ℂ`-algebra isomorphism carries `twoEdge`'s left-hand side onto a
*single* `ε`-block: a single block is indexed by the `τ`'s over one maximal ideal, a subsingleton
here, so it has `ℂ`-dimension at most `1`, while the left-hand side has dimension `2`. This is
exactly the gap finding F-2 identified, and it is why the corrected statement sums over
`Specm {}_iM_j`.

@census none (regression witness for verification finding F-2)
-/
theorem twoEdge_no_single_block_equiv {E : Type} [Subsingleton E] :
    IsEmpty ((ℂ ⊗[ℂ] (Fin 2 → ℂ)) ≃ₐ[ℂ] (E → ℂ)) := by
  refine ⟨fun f => ?_⟩
  have h2 : Module.finrank ℂ (ℂ ⊗[ℂ] (Fin 2 → ℂ)) = 2 := twoEdge_finrank_lhs
  have hle : Module.finrank ℂ (E → ℂ) ≤ 1 := by
    haveI : Finite E := Finite.of_subsingleton
    haveI := Fintype.ofFinite E
    rw [Module.finrank_pi]
    simpa using Fintype.card_le_one_iff_subsingleton.mpr ‹Subsingleton E›
  have := f.toLinearEquiv.finrank_eq
  omega

/-! ### `Γ_K(S)` -/

/-- **Definition** (the `K`-rational quiver associated to an étale `K`-species; unlabelled in the
source, census `RQ2-2.12`).
For an étale `K`-species `S` and a splitting field `L` of `S` (finite Galois over `K`, the §2.3
standing hypothesis), `Γ_K(S) := (V,E,s,t)` with `V = ⨆_i Hom_K(L_i,L)`,
`E = ⨆_{i,j} ⨆_{ε ∈ Specm {}_iM_j} Hom_K(L_ε,L)`, `s(τ) = τ ∘ τ_ε`, `t(τ) = τ ∘ σ_ε`, together
with its canonical `Gal(L/K)`-structure.

@census    RQ2-2.12
@source    def:quiverofspecies
@clauses   RQ2-2.12-H1, RQ2-2.12-H2, RQ2-2.12-C1, RQ2-2.12-C2, RQ2-2.12-C3, RQ2-2.12-C4, RQ2-2.12-C5,
           RQ2-2.12-C6, RQ2-2.12-C7, RQ2-2.12-C8, RQ2-2.12-C9
@imports   none
@divergence JUSTIFIED_REFORMULATION on clause `RQ2-2.12-C3` only. The source's
`{}_iM_j ⊗_{L_j} L` presupposes an `L_j`-algebra structure on `L`, of which there is no canonical
choice (`Hom_K(L_j,L)` is a `Gal(L/K)`-torsor — this is `RQ2-2.10`); the decomposition is therefore
stated for an arbitrary embedding `ι : L_j → L`, universally quantified
(`etaleBialgebra_decomposition`), which is the source's implicit choice made explicit and is
strictly stronger than the source's single instance of it. The tensor factors are also written in
mathlib's order, `L ⊗_{L_j} {}_iM_j` for the source's `{}_iM_j ⊗_{L_j} L` — the same reformulation
stage S3 recorded on `RQ2-2.05`, and for the same reason: mathlib carries the `L`-algebra instance
on the left factor. Everything else is literal: `V` and `E`
are the two disjoint unions (`C1`, `C4`), `τ_ε`/`σ_ε` are the composites of the structure maps with
the residue map (`C5`), `s` and `t` are precomposition with them (`C6`, `C7`) and are equivariant by
`rfl` (`C8`), and the result is a `K`-rational quiver in the sense of `RQ2-1.02` (`C9`), its
continuity conditions being vacuous because the standing hypothesis `hL` makes `L/K` finite.
Clause `RQ2-2.12-H1` is the argument `S`, clause `RQ2-2.12-H2` the argument `hL`.
Finally, and disclosed here under verification finding C-8 in the wording `RQ2-2.09-C7` already uses:
the source's `⊕_{ε ∈ Specm} ∏_τ` is realised as the **single product** over
`Σ ε : Specm {}_iM_j, Hom_{L_j}(L_ε,L)`. `Specm {}_iM_j` is finite (`{}_iM_j` is a finite étale
`K`-algebra, hence Artinian), and over a finite index set the direct sum and the direct product of
the summands coincide, so this is the same object; the product form is the one carrying mathlib's
instances. Same reformulation, same reason, as on `RQ2-2.09-C7`.
-/
noncomputable def toRationalQuiver (hL : S.IsSplitBy L) : RationalQuiver K L :=
  haveI := hL.galois
  haveI := hL.findim
  RationalQuiver.ofAction K L
    { V := S.vertexSet L
      E := S.edgeSet L
      source := S.edgeSource L
      target := S.edgeTarget L
      finite_V := S.finite_vertexSet L
      finite_E := S.finite_edgeSet L }
    (toPermHom Gal(L/K) (S.vertexSet L)) (toPermHom Gal(L/K) (S.edgeSet L))
    (fun σ e => (S.edgeSource_smul L σ e).symm) (fun σ e => (S.edgeTarget_smul L σ e).symm)
    (IsSmooth.of_discreteTopology _) (IsSmooth.of_discreteTopology _)

end EtaleSpecies

end RationalQuivers
