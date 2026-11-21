import DstDiophantine.Gravity.NuclearLayer
import DstDiophantine.Gravity.ShieldCeiling

/-!
# Layer positions, node clearance, and binding energy
-/

namespace Goals.Gravity

/-- **Claim (EN):** Every physical sample stays a full step away from a node
    (not only the first node cap).

    **Claim (JA):** すべての物理サンプルが節から一歩離れた刻みにあり続ける（最初の節の上限だけでなく）。

    **Paper:** site `renormalization.html`.

    **Status:** open.
-/
theorem all_samples_full_step_from_node : True := by sorry

/-- **Claim (EN):** Binding energy is derived from the first-node clearance cap.

    **Claim (JA):** 結合エネルギーが最初の節のクリアランス上限から導かれる。

    **Paper:** site `renormalization.html`.

    **Status:** open.
-/
theorem binding_energy_from_first_node_cap : True := by sorry

/-- **Claim (EN):** Finite height of channel walls (layer positions fixed).

    **Claim (JA):** チャネル壁の有限の高さ（層の位置が決まる）。

    **Paper:** site `renormalization.html`.

    **Status:** open.
-/
theorem finite_wall_height_layer_positions : True := by sorry

end Goals.Gravity