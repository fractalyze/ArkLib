/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Stateless query implementations

`AppendCounterexample.lean` shows `Reduction.append_completeness` is false for a general
`impl : QueryImpl oSpec (StateT σ ProbComp)`: `Reduction.append` runs both provers before both
verifiers, so `P₂` can leave state that `V₁` then reads.

`IsStateless` is the hypothesis that rules exactly that out — the handler factors through
`ProbComp`, so no party can signal to a later one through `σ`.
-/

open OracleComp OracleSpec

namespace QueryImpl

variable {ι σ : Type} {spec : OracleSpec ι}

/-- `impl` is **stateless**: every query is answered by a `ProbComp` lifted into `StateT σ`,
so answering a query neither reads nor writes `σ`. -/
def IsStateless (impl : QueryImpl spec (StateT σ ProbComp)) : Prop :=
  ∃ impl₀ : QueryImpl spec ProbComp, ∀ q, impl q = liftM (impl₀ q)

/-- The witness of `IsStateless`. -/
noncomputable def IsStateless.base {impl : QueryImpl spec (StateT σ ProbComp)}
    (h : impl.IsStateless) : QueryImpl spec ProbComp := h.choose

lemma IsStateless.apply {impl : QueryImpl spec (StateT σ ProbComp)} (h : impl.IsStateless)
    (q : spec.Domain) : impl q = liftM (h.base q) := h.choose_spec q

/-- **A stateless handler's simulation does not depend on the initial state.** Running
`simulateQ` under a stateless `impl` and discarding the final state gives the `ProbComp`
obtained from the underlying handler, for every `s`. -/
lemma simulateQ_run'_of_isStateless {impl : QueryImpl spec (StateT σ ProbComp)}
    (h : impl.IsStateless) {α : Type} (oa : OracleComp spec α) (s : σ) :
    (simulateQ impl oa).run' s = simulateQ h.base oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    show (fun x : α × σ => x.1) <$> (pure (a, s) : ProbComp (α × σ)) = pure a
    simp
  | query_bind t oa ih =>
    simp only [simulateQ_query_bind, h.apply]
    show (fun x : α × σ => x.1) <$>
        ((h.base t >>= fun u => (pure (u, s) : ProbComp _)) >>=
          fun p => (simulateQ impl (oa p.1)) p.2) = _
    simp only [bind_assoc, pure_bind, map_bind]
    exact bind_congr fun u => ih u

/-- Adding a `ProbComp` handler to a stateless one keeps it stateless: `addLift` lifts both
sides into the target monad, and neither reads nor writes `σ`. -/
lemma IsStateless.addLift {ι₂ : Type} {spec₂ : OracleSpec ι₂}
    {impl : QueryImpl spec (StateT σ ProbComp)} (h : impl.IsStateless)
    (impl₂ : QueryImpl spec₂ ProbComp) :
    (impl.addLift impl₂ : QueryImpl (spec + spec₂) (StateT σ ProbComp)).IsStateless :=
  ⟨(h.base.addLift impl₂ : QueryImpl (spec + spec₂) ProbComp), by
    rintro (t | t)
    · show (impl t : StateT σ ProbComp _) = _
      rw [h.apply]; rfl
    · rfl⟩

end QueryImpl
