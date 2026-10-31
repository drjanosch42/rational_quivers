module

public import RQPalomar.Bridge

/-!
# Solution

The compared theorems of `Challenge.lean`, proved from the formalization `RationalQuivers`
(Theorem B: `RationalQuivers.Gelfand.gelfand_equivalence`) through `RQPalomar/Bridge.lean`.
-/

public section

namespace RQStatement.Palomar
open RQStatement.HC RQStatement.Gelfand CategoryTheory

theorem theoremB (E : Type) [Field E] [CharZero E] (D : ImagUnit E) (ℓ : ℕ) :
    Nonempty (HC ℓ E D ≌ (RepNilTarget D ℓ).FullSubcategory) :=
  RQBridge.theoremB E D ℓ

theorem imagUnit_nonempty (E : Type) [Field E] : Nonempty (ImagUnit E) :=
  RQBridge.imagUnit_nonempty E

end RQStatement.Palomar
