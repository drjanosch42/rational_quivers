import RationalQuivers.HC.ImagUnit
import RationalQuivers.Quiver.OfSign

/-!
# `χ_E` and the sign-character Gelfand quiver

A **leaf** module (only the root aggregator and the instrument
import it): it supplies the inhabitant of the hypotheses of
`RationalQuiver.gelfandOfSign_eq_gelfandOfCardTwo` (`|Gal(L/K)| = 2`, `χ` injective) by `χ_E` of an `ImagUnit`, instantiated at `ImagUnit.real`.  It is kept out of
`HC/ImagUnit.lean` so that the `Quiver/` modules do not enter the import closure of `HC/` (the
load order of the downstream `Gelfand/GeneralField/Identification*` modules is sensitive to it).
-/

namespace RationalQuivers.HC

namespace ImagUnit

variable {E : Type} [Field E] (D : ImagUnit E)

section CharZero

variable [CharZero E]

/-! ### `Γ_D` and `gelfandOfCardTwo` -/

/-- **`Γ_D` vs `gelfandOfCardTwo`**: the hypotheses of
`RationalQuiver.gelfandOfSign_eq_gelfandOfCardTwo` — `|G_E| = 2` and `χ` injective — are supplied by
`χ_E` whenever `√-1 ∉ E`.  @census none (helper) -/
theorem gelfandOfSign_eq_gelfandOfCardTwo (h : ¬ ∃ a : E, a * a = -1) :
    RationalQuiver.gelfandOfSign E D.L D.chiHom
      = RationalQuiver.gelfandOfCardTwo E D.L (D.card_gal_of_not_sqrt h) :=
  RationalQuiver.gelfandOfSign_eq_gelfandOfCardTwo E D.L (D.card_gal_of_not_sqrt h)
    D.chiHom_injective

end CharZero

end ImagUnit

/-- The inhabitant at `ImagUnit.real` (`ℂ/ℝ`, `√-1 ∉ ℝ`).  @census none (helper) -/
theorem ImagUnit.real_gelfandOfSign :
    RationalQuiver.gelfandOfSign ℝ ImagUnit.real.L ImagUnit.real.chiHom
      = RationalQuiver.gelfandOfCardTwo ℝ ImagUnit.real.L
          (ImagUnit.real.card_gal_of_not_sqrt ImagUnit.real_not_sqrt) :=
  ImagUnit.real.gelfandOfSign_eq_gelfandOfCardTwo ImagUnit.real_not_sqrt

end RationalQuivers.HC
