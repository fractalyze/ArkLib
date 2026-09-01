/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import VCVio

/-!
# Composing two lower bounds across a bind

Security definitions in this library are stated as `Pr[good | …] ≥ 1 - ε`. Composing two
such statements needs the dual of `probEvent_bind_le_of_forall_le`: a *lower* bound on a
bind, given a lower bound on the prefix and a uniform lower bound on the continuation over
the prefix's good outcomes.

The errors add, as one expects, and the proof is the usual
`(1 - ε₂)(1 - ε₁) ≥ 1 - (ε₁ + ε₂)` slack argument carried out in `ℝ≥0∞`, where subtraction
truncates.
-/

open OracleComp ENNReal

namespace OracleComp

variable {α β : Type}

/-- `(1 - b) * x ≥ x - b` whenever `x ≤ 1`: scaling down by `1 - b` costs at most `b`. -/
private lemma sub_le_one_sub_mul {x b : ℝ≥0∞} (hx : x ≤ 1) : x - b ≤ (1 - b) * x := by
  by_cases hb : 1 ≤ b
  · simpa [tsub_eq_zero_of_le (hx.trans hb)] using zero_le _
  · push_neg at hb
    rw [ENNReal.sub_mul (by intro _ _; exact ne_top_of_le_ne_top one_ne_top hx), one_mul]
    exact tsub_le_tsub_left (mul_le_of_le_one_right' hx) x

/-- **Composing completeness-style bounds across a bind.** If the prefix lands in `P` except
with probability `ε₁`, and from every `P`-outcome the continuation lands in `Q` except with
probability `ε₂`, then the composite lands in `Q` except with probability `ε₁ + ε₂`.

The dual of `probEvent_bind_le_of_forall_le`, which bounds a bind from above. -/
lemma one_sub_le_probEvent_bind {mx : ProbComp α} {f : α → ProbComp β}
    {P : α → Prop} {Q : β → Prop} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : 1 - ε₁ ≤ Pr[ P | mx])
    (h₂ : ∀ a, P a → 1 - ε₂ ≤ Pr[ Q | f a]) :
    1 - (ε₁ + ε₂) ≤ Pr[ Q | mx >>= f] := by
  classical
  rw [probEvent_bind_eq_tsum]
  have key : (1 - ε₂) * Pr[ P | mx] ≤ ∑' a, Pr[= a | mx] * Pr[ Q | f a] := by
    rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun a => ?_
    by_cases hP : P a
    · rw [if_pos hP, mul_comm]
      exact mul_le_mul' le_rfl (h₂ a hP)
    · simp [hP]
  refine le_trans ?_ (le_trans (mul_le_mul' (le_refl (1 - ε₂)) h₁) key)
  calc 1 - (ε₁ + ε₂) = (1 - ε₁) - ε₂ := by rw [tsub_add_eq_tsub_tsub]
    _ ≤ (1 - ε₂) * (1 - ε₁) := sub_le_one_sub_mul tsub_le_self

end OracleComp
