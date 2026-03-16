/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: bad74acb-42b2-49d7-8165-f16722ac5092

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem geometric_decay_exists_nat
    (d m : ℕ) (hd_pos : 0 < d) (hle : d < m)
    (ε : ℝ≥0∞) (hε_pos : 0 < ε) :
    ∃ t : ℕ, (d / m : ℝ≥0∞) ^ t ≤ ε
-/

/-
Target: For any ε > 0 and ratio r < 1, there exists t such that r^t ≤ ε.

Key insight: For 0 < r < 1, lim_{t→∞} r^t = 0, so eventually r^t < ε.

-/

import Mathlib.Tactic
import Mathlib.Data.ENNReal.Basic


noncomputable section

open scoped ENNReal

section MainTheorem

/-- **Main Theorem**: Geometric decay eventually reaches any threshold.

    For d < m (so d/m < 1) and any ε > 0, there exists t such that (d/m)^t ≤ ε.

    PROVE THIS THEOREM.
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
theorem geometric_decay_exists_nat
    (d m : ℕ) (hd_pos : 0 < d) (hle : d < m)
    (ε : ℝ≥0∞) (hε_pos : 0 < ε) :
    ∃ t : ℕ, (d / m : ℝ≥0∞) ^ t ≤ ε := by
  by_contra! h_contra;
  -- By the Archimedean property, since ε > 0 and (d/m)^t tends to 0 as t tends to infinity, there exists a t such that (d/m)^t < ε.
  have h_archimedean : Filter.Tendsto (fun t : ℕ => ((d : ℝ≥0∞) / m) ^ t) Filter.atTop (nhds 0) := by
    -- Since $d < m$, we have $d / m < 1$, and thus $(d / m)^t$ tends to $0$ as $t$ tends to infinity.
    have h_lt_one : (d : ℝ≥0∞) / m < 1 := by
      rw [ ENNReal.div_lt_iff ] <;> norm_num [ hd_pos, hle ];
      grind;
    exact ENNReal.tendsto_pow_atTop_nhds_zero_iff.mpr h_lt_one
  exact absurd ( h_archimedean.eventually ( gt_mem_nhds hε_pos ) ) fun h => by obtain ⟨ t, ht ⟩ := h.exists; exact ht.not_le ( le_of_lt ( h_contra t ) ) ;

end MainTheorem
