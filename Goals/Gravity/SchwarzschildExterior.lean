import DstDiophantine.Gravity.Perihelion
import DstDiophantine.Gravity.ClassicalSchwarzschild
import DstDiophantine.Gravity.SI

/-!
# Schwarzschild exterior — observational targets

Proved coefficient structure lives in `Perihelion` and `ClassicalSchwarzschild`.
These goals connect bounds to solar-system tests named as open on the site and
in `papers/double-spacetime-theory.tex`.
-/

namespace Goals.Gravity

open DstDiophantine.Gravity
open Real

/-- **Claim (EN):** Mercury's observed perihelion advance (~43 arcseconds per
    century) is obtained from the exterior DST radial-return bounds and solar
    orbital parameters.

    **Claim (JA):** 水星の観測される近日点移動（約 43 秒角／世紀）が、外側 DST の
    動径回りの評価と太陽系の軌道定数から得られる。

    **Paper:** `papers/double-spacetime-theory.tex`; site `gravity.html`
    (current scope).

    **Status:** open — builds on proved perihelion lemmas; SI inputs external.
-/
theorem mercury_perihelion_arcsec_per_century :
    ∃ Δ : ℝ, (42 : ℝ) < Δ ∧ Δ < (44 : ℝ) := by sorry

/-- **Claim (EN):** Weak-field light deflection around the Sun matches the
    classical GR angle at leading order.

    **Claim (JA):** 太陽周りの弱い場での光の偏向が、主要項で古典的 GR と一致する。

    **Paper:** `papers/double-spacetime-theory.tex`.

    **Status:** open — no unified null integration through the freeze chart yet
    (`Gravity.Lensing` paper boundary).
-/
theorem solar_light_deflection_weak_field :
    ∃ θ_deflect : ℝ, 0 < θ_deflect := by sorry

/-- **Claim (EN):** Perihelion and lensing extend to rotating masses.

    **Claim (JA):** 近日点・レンズ効果が回転する質量へ拡張される。

    **Paper:** site `gravity.html`.

    **Status:** open.
-/
theorem rotating_mass_exterior_tests : True := by sorry

/-- **Claim (EN):** Interior clock rates tied by light signals are read
    consistently with the deep-interior DST surplus.

    **Claim (JA):** 光信号で結ばれた内部時計の進みが、体深部の DST 余剰と整合的に読める。

    **Paper:** site `gravity.html` (limits).

    **Status:** open.
-/
theorem interior_clock_exchange_consistency : True := by sorry

end Goals.Gravity