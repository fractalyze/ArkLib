/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import VCVio

/-!
# Splitting an upper bound across a bind on a prefix event

Soundness definitions in this library are stated as `Pr[bad | …] ≤ ε`. Composing two of them
along a sequential run needs a union bound that is *not* uniform in the prefix: the
continuation's bound only holds on the outcomes where the prefix already failed to be bad.

`probEvent_bind_le_add` is that bound. It is the union-bound counterpart of
`one_sub_le_probEvent_bind` in `CompletenessBound.lean`, which composes lower bounds.
-/

open OracleComp ENNReal

namespace OracleComp

variable {α β : Type}

/-- **Splitting a bind's bad event on a prefix event.** If the continuation lands in `Q` with
probability at most `ε` from every prefix outcome outside `P`, then the composite lands in `Q`
with probability at most `Pr[P | prefix] + ε` -- the prefix's own bad event plus the
continuation's error.

The two sequential-composition soundness theorems instantiate `P` as "the intermediate statement
is in the intermediate language", which is exactly the first verifier's bad event and exactly the
second's hypothesis. -/
lemma probEvent_bind_le_add {mx : ProbComp α} {f : α → ProbComp β}
    (P : α → Prop) {Q : β → Prop} {ε : ℝ≥0∞} (h : ∀ a, ¬ P a → Pr[ Q | f a] ≤ ε) :
    Pr[ Q | mx >>= f] ≤ Pr[ P | mx] + ε := by
  classical
  rw [probEvent_bind_eq_tsum]
  have hpt : ∀ a : α, Pr[= a | mx] * Pr[ Q | f a]
      ≤ (if P a then Pr[= a | mx] else 0) + (if P a then 0 else Pr[= a | mx] * ε) := by
    intro a
    by_cases hP : P a
    · simp [hP]
    · simp only [hP, if_false, zero_add]
      exact mul_le_mul' (le_refl Pr[= a | mx]) (h a hP)
  have hdrop : ∀ a : α, (if P a then 0 else Pr[= a | mx] * ε) ≤ Pr[= a | mx] * ε := by
    intro a; split <;> simp
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_add, probEvent_eq_tsum_ite]
  refine add_le_add (le_refl _) (le_trans (ENNReal.tsum_le_tsum hdrop) ?_)
  rw [ENNReal.tsum_mul_right]
  simp


/-- **Splitting an event on an unrelated predicate.** Subadditivity in its simplest form: the
bad event is covered by its two halves. Unlike `probEvent_bind_le_add` the predicate need not be
decided by a prefix -- the two halves may then be bounded by different decompositions of the same
computation. -/
lemma probEvent_le_add_split {mx : ProbComp α} (P Q : α → Prop) :
    Pr[ Q | mx] ≤ Pr[ fun a => Q a ∧ P a | mx] + Pr[ fun a => Q a ∧ ¬ P a | mx] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hQ : Q a <;> by_cases hP : P a <;> simp [hQ, hP]

end OracleComp
