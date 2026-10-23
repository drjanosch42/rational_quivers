import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.Module.Equiv.Defs

/-!
# Galois descent: semi-linear maps

Formalizes the semi-linearity vocabulary of §1.1 of `latex/rational_quivers.tex`
(census `RQ2-1.15`).

## Main definitions / results
* `RationalQuivers.Descent.IsSemilinear` — the paper's `σ`-linearity predicate
  (`UNLABELED-semilinear`, census `RQ2-1.15`).
* `RationalQuivers.Descent.isSemilinear_of_semilinearMap`,
  `RationalQuivers.Descent.toSemilinearMap` — bridges to mathlib's bundled semi-linear maps
  `V →ₛₗ[σ] W` (helpers, no census row).

## Implementation notes
The paper defines `σ`-linearity as a property of a *bare map* `φ : V → W`
(`φ (α · v) = σ(α) φ(v)`); it does not require additivity as part of the definition.  mathlib's
`LinearMap` with a semi-linear `RingHom` (`V →ₛₗ[σ] W`) is the *bundled additive* notion, so it
cannot literally express the paper's predicate.  Following `CONVENTIONS.md` §6 ladder step 3 we
define the predicate and *bridge* to mathlib in both directions rather than forking mathlib's
notion; see `workflow/ledger/MATHLIB-DECISIONS.tsv` row `MD-S0-01`.
-/

universe u v w

namespace RationalQuivers.Descent

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {V : Type v} {W : Type w}
variable [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]

/-- **Semi-linear map** (`UNLABELED-semilinear`, §1.1 of the source).

For `σ ∈ Gal(L/K)` and `L`-vector spaces `V`, `W`, a map `φ : V → W` is *semi-linear with respect
to `σ`* (or simply *`σ`-linear*) if `φ (α · v) = σ(α) · φ(v)` for all `v ∈ V` and all `α ∈ L`.

@census    RQ2-1.15
@source    def:semilinear
@clauses   RQ2-1.15-H1, RQ2-1.15-H2, RQ2-1.15-C1
@imports   none
@divergence none
-/
def IsSemilinear (σ : Gal(L/K)) (φ : V → W) : Prop :=
  ∀ (a : L) (v : V), φ (a • v) = σ a • φ v

/-- Helper (bridge to mathlib, no census row): every bundled `σ`-semi-linear map in mathlib's
sense `V →ₛₗ[σ] W` is `σ`-linear in the sense of `IsSemilinear`.

@census    none
-/
theorem isSemilinear_of_semilinearMap (σ : Gal(L/K))
    (f : V →ₛₗ[(σ.toRingEquiv.toRingHom : L →+* L)] W) :
    IsSemilinear σ (f : V → W) := fun a v => map_smulₛₗ f a v

/-- Helper (bridge to mathlib, no census row): an *additive* map that is `σ`-linear in the sense
of `IsSemilinear` is a bundled semi-linear map `V →ₛₗ[σ] W`.

@census    none
-/
def toSemilinearMap (σ : Gal(L/K)) (φ : V →+ W) (h : IsSemilinear σ φ) :
    V →ₛₗ[(σ.toRingEquiv.toRingHom : L →+* L)] W where
  toFun := φ
  map_add' := φ.map_add
  map_smul' := h

@[simp]
theorem coe_toSemilinearMap (σ : Gal(L/K)) (φ : V →+ W) (h : IsSemilinear σ φ) :
    (toSemilinearMap σ φ h : V → W) = φ := rfl

end RationalQuivers.Descent
