/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Composition.Sequential.HandlerCommutativity
import ArkLib.ToVCVio.EvalDist.CompletenessBound

/-!
# Repairing `Reduction.append_completeness`

`AppendCounterexample.lean` shows the theorem is false as stated, and
`HandlerCommutativity.lean` isolates the hypothesis that repairs it. This file holds the
execution-side groundwork joining the two.

`Reduction.append_run_run` puts the appended reduction's run in sequential form: `P₁, P₂,
V₁, V₂`. That order is the whole problem — `Reduction.run` runs the entire prover before the
entire verifier, whereas running `R₁` and then `R₂` interleaves them, and for a handler that
can report the order it was called in the two differ. `QueryImpl.IsCommutative` is what makes
them agree, and `OracleComp.one_sub_le_probEvent_bind` is what adds the two completeness
errors once they do.
-/

open OracleComp OracleSpec ProtocolSpec

/-- `OptionT.run` of a bind whose prefix cannot fail: the lift disappears and the prefix
becomes an ordinary bind in the base monad. The provers never fail, so this is what strips
`OptionT` off `Prover.run` and leaves a plain `OracleComp` bind chain for the commutativity
lemmas to work on. -/
lemma OptionT.run_liftM_bind {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (x : m α) (f : α → OptionT m β) :
    ((liftM x : OptionT m α) >>= f).run = x >>= fun a => (f a).run := by
  simp [OptionT.run_bind, Option.elimM]

/-- `OptionT.run` of a bind whose prefix is an `Option` injected by `getM`: the `Option` is
already known, so the bind is the corresponding case split. -/
lemma OptionT.run_getM_bind {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (x : Option α) (f : α → OptionT m β) :
    ((x.getM : OptionT m α) >>= f).run = x.elim (pure none) fun a => (f a).run := by
  cases x <;> simp [Option.getM]

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {m n : ℕ}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- The appended protocol's ambient computation monad, named so the statement below fits on a
line. -/
private abbrev Comp (oSpec : OracleSpec ι) (pSpec₁ : ProtocolSpec m) (pSpec₂ : ProtocolSpec n) :=
  OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)

/-- **The appended reduction, run.** `Prover.append_run` puts the two provers in sequence;
this carries that through `Reduction.run` and `Verifier.append` to the whole reduction, so the
appended run reads as `P₁, P₂, V₁, V₂` with the transcript split back apart for the verifiers.

The order is the point. `Reduction.run` runs the whole prover and *then* the whole verifier,
so `P₂` precedes `V₁` here, whereas running `R₁` and then `R₂` interleaves them. Turning one
into the other is what needs `QueryImpl.IsCommutative`; see `AppendCounterexample.lean` for
why nothing weaker will do. -/
theorem append_run_run (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) (stmt : Stmt₁) (wit : Wit₁) :
    (Reduction.run stmt wit (R₁.append R₂)).run
      = OptionT.run (m := Comp oSpec pSpec₁ pSpec₂) (do
          let x ← (liftM ((liftM (Prover.run stmt wit R₁.prover) :
                Comp oSpec pSpec₁ pSpec₂ _)) : OptionT (Comp oSpec pSpec₁ pSpec₂) _)
          let y ← (liftM ((liftM (Prover.run x.2.1 x.2.2 R₂.prover) :
                Comp oSpec pSpec₁ pSpec₂ _)) : OptionT (Comp oSpec pSpec₁ pSpec₂) _)
          let stmtOut ← (liftM ((liftM (do
                let s₂ ← R₁.verifier.verify stmt x.1
                R₂.verifier.verify s₂ y.1).run : Comp oSpec pSpec₁ pSpec₂ _)) :
                  OptionT (Comp oSpec pSpec₁ pSpec₂) _)
          let s₃ ← stmtOut.getM
          pure ((x.1 ++ₜ y.1, y.2.1, y.2.2), s₃)) := by
  unfold Reduction.run Reduction.append
  dsimp only
  rw [Prover.append_run]
  simp only [Verifier.append, Verifier.run, liftM_bind, liftM_pure, bind_assoc, pure_bind,
    FullTranscript.append_fst, FullTranscript.append_snd, monadLift_liftM_OptionT]

/-- The same run with `OptionT` stripped off the provers: a plain `OracleComp` bind chain,
`P₁` then `P₂` then the verifier block, with the failure bookkeeping as one `Option.elim` at
the end. This is the form `QueryImpl.IsCommutative.bind_prefix` matches. -/
theorem append_run_run_flat (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) (stmt : Stmt₁) (wit : Wit₁) :
    (Reduction.run stmt wit (R₁.append R₂)).run
      = (do
          let x ← (liftM (Prover.run stmt wit R₁.prover) : Comp oSpec pSpec₁ pSpec₂ _)
          let y ← (liftM (Prover.run x.2.1 x.2.2 R₂.prover) : Comp oSpec pSpec₁ pSpec₂ _)
          let o ← (liftM (do
            let s₂ ← R₁.verifier.verify stmt x.1
            R₂.verifier.verify s₂ y.1).run : Comp oSpec pSpec₁ pSpec₂ _)
          Option.elim o (pure none)
            fun s₃ => pure (some ((x.1 ++ₜ y.1, y.2.1, y.2.2), s₃))) := by
  rw [append_run_run]
  simp only [OptionT.run_liftM_bind, OptionT.run_getM_bind, OptionT.run_pure]

section ChallengeRestrict

variable {σ : Type} [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]
  {impl : QueryImpl oSpec (StateT σ ProbComp)} {α : Type}

/-- Transporting a uniform sample along an equality of types is again a uniform sample. Both
`SampleableType` instances are uniform by their own axioms, and `cast` is a bijection, so the two
agree pointwise -- which is all `evalDist_ext` needs. The instances themselves are unrelated: the
appended protocol's instance is built by `Fin.fappend₂`, not by transporting the component's, so
this is not definitional. -/
lemma evalDist_cast_map_uniformSample {A B : Type} [SampleableType A] [SampleableType B]
    (h : A = B) : 𝒟[(cast h <$> ($ᵗ A) : ProbComp B)] = 𝒟[($ᵗ B)] :=
  evalDist_ext fun x =>
    probOutput_map_bijective_uniform_cross A (cast h) (Equiv.cast h).bijective x

/-- The handler `Reduction.completeness` runs a protocol under: the ambient `impl` for `oSpec`,
uniform sampling for the challenges. Named so the statements below can say which protocol's
challenge oracle they mean. -/
private abbrev pImplOf {N : ℕ} (pSpec : ProtocolSpec N)
    [∀ i, SampleableType (pSpec.Challenge i)] (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
  QueryImpl.addLift impl challengeQueryImpl

/-- **Restricting the challenge oracle.** A computation of the left component, lifted into the
appended protocol's challenge spec and run under the appended handler, has the same distribution
as the same computation run under the left component's own handler. The `oSpec` queries are
untouched by the lift; a challenge query is reindexed to `ChallengeIdx.inl`, where the response
transport is a `cast` and `evalDist_cast_map_uniformSample` says the sample is unchanged. -/
lemma evalDist_simulateQ_liftM_left (c : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α) (s : σ) :
    𝒟[StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
          (liftM c : Comp oSpec pSpec₁ pSpec₂ α)) s]
      = 𝒟[StateT.run (simulateQ (pImplOf pSpec₁ impl) c) s] := by
  induction c using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t oa ih =>
    rw [liftM_bind]
    simp only [simulateQ_bind, StateT.run_bind, evalDist_bind]
    have hhead : 𝒟[StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
          (liftM (liftM (OracleSpec.query t) :
            OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _) : Comp oSpec pSpec₁ pSpec₂ _)) s]
        = 𝒟[StateT.run (simulateQ (pImplOf pSpec₁ impl)
            (liftM (OracleSpec.query t) : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)) s] := by
      rcases t with t | t
      · rfl
      · obtain ⟨i, q⟩ := t
        conv_lhs => rw [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_query]
        have hkey := evalDist_cast_map_uniformSample (challenge_append_inl (pSpec₂ := pSpec₂) i)
        rw [evalDist_map] at hkey
        have hfin : (fun a => (cast (challenge_append_inl (pSpec₂ := pSpec₂) i) a, s)) <$>
              𝒟[($ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i)))]
            = (fun a => (a, s)) <$> 𝒟[($ᵗ (pSpec₁.Challenge i))] := by
          rw [← hkey, Functor.map_map]
        -- `simp only` with the resolved lemma list leaves the goal in a shape `exact` rejects;
        -- the unfoldings (`pImplOf`, `OracleSpec.query`) are what make the two sides defeq.
        simp [pImplOf, simulateQ_liftM_query, OracleSpec.query]
        exact hfin
    rw [hhead]
    exact bind_congr fun p => ih p.1 p.2

end ChallengeRestrict

end Reduction
