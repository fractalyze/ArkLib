/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Commutative and stateless query handlers

`AppendCounterexample.lean` shows `Reduction.append_completeness` is false for a general
`impl : QueryImpl oSpec (StateT σ ProbComp)`: `Reduction.append` runs both provers before both
verifiers, so `P₂` can leave state that `V₁` then reads.

`IsCommutative` is the hypothesis that rules exactly that out, and it is the one the
`TODO` above `append_completeness` asks for. It says two computations that do not read each
other's results may be simulated in either order without changing the joint distribution of
their results and the resulting state.

`IsStateless` — the handler factors through `ProbComp` — is the easy sufficient condition,
and it is what a handler for the empty spec satisfies for free. It is *not* the right
headline hypothesis: a cache-backed random oracle is stateful and yet commutative, and
`randomOracle` is exactly the instantiation composition most needs to cover.
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

/-- **A stateless handler threads the state unchanged.** Simulating under a stateless `impl`
returns the `ProbComp` of the underlying handler paired with the *initial* state — nothing a
computation does can be observed later through `σ`. -/
lemma simulateQ_run_of_isStateless {impl : QueryImpl spec (StateT σ ProbComp)}
    (h : impl.IsStateless) {α : Type} (oa : OracleComp spec α) (s : σ) :
    (simulateQ impl oa).run s = (fun a => (a, s)) <$> simulateQ h.base oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => show (pure (a, s) : ProbComp (α × σ)) = _; simp
  | query_bind t oa ih =>
    simp only [simulateQ_query_bind, h.apply]
    show ((h.base t >>= fun u => (pure (u, s) : ProbComp _)) >>=
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

/-- The state-discarding form of `simulateQ_run_of_isStateless`. -/
lemma simulateQ_run'_of_isStateless {impl : QueryImpl spec (StateT σ ProbComp)}
    (h : impl.IsStateless) {α : Type} (oa : OracleComp spec α) (s : σ) :
    (simulateQ impl oa).run' s = simulateQ h.base oa := by
  show (fun x : α × σ => x.1) <$> (simulateQ impl oa).run s = _
  rw [simulateQ_run_of_isStateless h]
  simp

/-! ## Commutativity -/

/-- `impl` answers queries **commutatively**: two computations, neither of which reads the
other's result, may be simulated in either order without changing the joint distribution of
their results *and* of the resulting state.

This is the hypothesis `Reduction.append_completeness` actually needs.
`AppendCounterexample.lean`'s handler fails it in the sharpest way — it returns the old flag
and sets a new one, so it *reports* the order it was called in.

Two design points:

* **The state is part of the claim.** Composition binds a further computation after the
  swap, and that continuation sees `σ`. Order-insensitive results over an order-*sensitive*
  state would still break the next step.
* **Weaker than statelessness, and deliberately so.** A cache-backed random oracle is
  stateful yet commutative: distinct queries get independent answers whatever the order, and
  the resulting cache holds the same entries. `IsStateless` would exclude it, and it is the
  case composition most needs to cover. -/
def IsCommutative (impl : QueryImpl spec (StateT σ ProbComp)) : Prop :=
  ∀ {α β : Type} (oa : OracleComp spec α) (ob : OracleComp spec β) (s : σ),
    𝒟[(simulateQ impl (do let a ← oa; let b ← ob; pure (a, b))).run s]
      = 𝒟[(simulateQ impl (do let b ← ob; let a ← oa; pure (a, b))).run s]

/-- A stateless handler is commutative: it collapses to a `ProbComp` handler, and `ProbComp`
binds commute by `evalDist_bind_comm`. The converse fails — see the docstring above. -/
lemma IsStateless.isCommutative {impl : QueryImpl spec (StateT σ ProbComp)}
    (h : impl.IsStateless) : impl.IsCommutative := by
  intro α β oa ob s
  rw [simulateQ_run_of_isStateless h, simulateQ_run_of_isStateless h]
  simp only [simulateQ_bind, simulateQ_pure, evalDist_map]
  exact congrArg _ (OracleComp.DeferredSampling.evalDist_bind_comm _ _ _)

/-- A handler for the **empty** oracle spec is stateless, hence commutative: there is no query
to answer, so there is nothing to carry through `σ`.

This is why the hypothesis is free for most current consumers —
`RingSwitching/Packing`, `Binius/BinaryBasefold` and `FRIBinius` all instantiate composition
at `oSpec = []ₒ`. `Sumcheck/Spec/General` is the one that carries a general `oSpec`. -/
lemma isStateless_of_isEmpty {σ : Type} (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    impl.IsStateless :=
  ⟨fun q => q.elim, fun q => q.elim⟩

lemma isCommutative_of_isEmpty {σ : Type} (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    impl.IsCommutative :=
  (isStateless_of_isEmpty impl).isCommutative

end QueryImpl
