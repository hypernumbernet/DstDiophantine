import DstDiophantine.Gravity.SignReversal
import DstDiophantine.Gravity.NuclearLength
import DstDiophantine.Gravity.NuclearLayer
import DstDiophantine.Gravity.MetalFusion

/-!
# Strong interaction / nuclear layers

Sign-reversal scale and channel length are partly capped in the main library;
binding energies, cross sections, and magic-number closure remain open in the
papers.
-/

namespace Goals.Gravity

open DstDiophantine.Gravity
open Real

/-- **Claim (EN):** Channel length ℓ and nuclear pull strength are pinned by
    scattering data without remaining free inputs.

    **Claim (JA):** チャネル長 ℓ と核引力の強さが、散乱データだけで自由入力なく決まる。

    **Paper:** `papers/dst-strong-interaction.tex`; site `layers.html`.

    **Status:** open — `SignReversal` treats r₁ as observational input.
-/
theorem derive_channel_length_from_scattering : True := by sorry

/-- **Claim (EN):** Yukawa carrier mass range from ℓ narrows to sharpen the
    pion mass comparison.

    **Claim (JA):** ℓ からの湯川担い手の質量の幅が狭まり、パイ中間子質量との比較が精密化する。

    **Paper:** site `layers.html`.

    **Status:** open.
-/
theorem yukawa_mass_range_refinement : True := by sorry

/-- **Claim (EN):** Neutron capture cross section grows as 1/v from the slow
    entrance mechanism.

    **Claim (JA):** 中性子捕獲断面積が、遅い入口機構から 1/v で増える。

    **Paper:** `papers/dst-strong-interaction.tex`.

    **Status:** open.
-/
theorem capture_cross_section_one_over_v : True := by sorry

/-- **Claim (EN):** Magic number closures (2, 8, 20, …) follow from seat counts
    on the layered gravitational channel.

    **Claim (JA):** 魔法数（2, 8, 20, …）が層状重力チャネルの席の数として導かれる。

    **Paper:** `papers/dst-strong-interaction.tex`; site `layers.html`.

    **Status:** open — seat formalism partial in main library.
-/
theorem magic_number_seat_closure : True := by sorry

/-- **Claim (EN):** Nucleon-pair forces across a touching surface sum to match
    Rutherford departures (e.g. gold ~9 fm).

    **Claim (JA):** 接触面をはさむ核子対の力の足し合わせが、ラザフォード則からのずれ（例：金 9 fm）と一致する。

    **Paper:** site `layers.html`.

    **Status:** open.
-/
theorem surface_touching_pair_force_sum : True := by sorry

/-- **Claim (EN):** Speed-dependent neutron skin and negative scattering lengths
    are derived from close-encounter amplitudes.

    **Claim (JA):** 速さ依存の中性子の皮と負の散乱長が、近距離遭遇の散乱振幅から導かれる。

    **Paper:** site `layers.html`.

    **Status:** open.
-/
theorem neutron_skin_scattering_amplitude : True := by sorry

/-- **Claim (EN):** Cold fusion entrance frequency from the octahedral seat
    (Pd cage) without fixing reaction rate or excess heat.

    **Claim (JA):** 正八面体席（Pd 空隙）から低温核融合入口の頻度がわかる（反応率・過剰熱は別）。

    **Paper:** `papers/dst-cold-fusion.tex`; site `layers.html`.

    **Status:** open — `MetalFusion` proves sign only.
-/
theorem cold_fusion_entrance_frequency : True := by sorry

end Goals.Gravity