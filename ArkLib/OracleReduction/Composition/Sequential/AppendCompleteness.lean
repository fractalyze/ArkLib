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

section SingleRun

variable {N : ℕ} {pSpec : ProtocolSpec N} {S W S' W' : Type}

/-- **One reduction, run, flattened out of `OptionT`.** The prover cannot fail, so `OptionT.run`
pushes past its bind and leaves a plain `OracleComp` chain: prover, verifier, one `Option.elim`.
The appended run is put in the same shape by `append_run_run_flat`, which is what lets the two
be compared. -/
theorem run_run_flat (R : Reduction oSpec S W S' W' pSpec) (stmt : S) (wit : W) :
    (Reduction.run stmt wit R).run
      = (do
          let x ← Prover.run stmt wit R.prover
          let o ← (liftM (R.verifier.verify stmt x.1).run :
              OracleComp (oSpec + [pSpec.Challenge]ₒ) _)
          Option.elim o (pure none) fun s' => pure (some (x, s'))) := by
  unfold Reduction.run
  simp only [Verifier.run, ← monadLift_liftM_OptionT, OptionT.run_liftM_bind,
    OptionT.run_getM_bind, OptionT.run_pure]

end SingleRun

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

/-- **The appended run with the two verifiers split apart.** `append_run_run_flat` leaves
`V₁ ; V₂` as one `OptionT` block; this pulls its failure bookkeeping out into the two
`Option.elim`s the swap has to commute past. -/
theorem append_run_run_split (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) (stmt : Stmt₁) (wit : Wit₁) :
    (Reduction.run stmt wit (R₁.append R₂)).run
      = (do
          let x ← (liftM (Prover.run stmt wit R₁.prover) : Comp oSpec pSpec₁ pSpec₂ _)
          let y ← (liftM (Prover.run x.2.1 x.2.2 R₂.prover) : Comp oSpec pSpec₁ pSpec₂ _)
          let o₂ ← (liftM (R₁.verifier.verify stmt x.1).run : Comp oSpec pSpec₁ pSpec₂ _)
          Option.elim o₂ (pure none) fun s₂ => do
            let o₃ ← (liftM (R₂.verifier.verify s₂ y.1).run : Comp oSpec pSpec₁ pSpec₂ _)
            Option.elim o₃ (pure none) fun s₃ =>
              pure (some ((x.1 ++ₜ y.1, y.2.1, y.2.2), s₃))) := by
  rw [append_run_run_flat]
  refine bind_congr fun x => bind_congr fun y => ?_
  simp only [OptionT.run_bind, Option.elimM, liftM_bind, bind_assoc]
  refine bind_congr fun o => ?_
  cases o <;> simp

section Recognise

variable (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
  (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)

/-- **The left phase is `R₁.run`.** In the swapped appended run, `P₁` followed by `V₁` is
exactly `R₁.run` lifted into the appended protocol, with the `Option` packaging left as an
outer `map` so the pair `(x, o₂)` -- which the appended run still needs -- survives. -/
theorem liftM_run_left_eq_map (stmt : Stmt₁) (wit : Wit₁) :
    (liftM ((Reduction.run stmt wit R₁).run) : Comp oSpec pSpec₁ pSpec₂ _)
      = (fun p => Option.elim p.2 none fun s₂ => some (p.1, s₂)) <$> (do
          let x ← (liftM (Prover.run stmt wit R₁.prover) : Comp oSpec pSpec₁ pSpec₂ _)
          let o₂ ← (liftM (R₁.verifier.verify stmt x.1).run : Comp oSpec pSpec₁ pSpec₂ _)
          pure (x, o₂)) := by
  rw [run_run_flat]
  simp only [liftM_bind, Prover.liftM_liftM_base, map_bind]
  refine bind_congr fun x => bind_congr fun o => ?_
  cases o <;> simp

/-- **The right phase is `R₂.run`.** The appended run carries `P₁`'s transcript into the
output; `R₂.run` does not, so the two differ by that one `map` -- which the completeness
event ignores. -/
theorem liftM_run_right_eq_map (s₂ : Stmt₂) (w₂ : Wit₂)
    (tr₁ : pSpec₁.FullTranscript) :
    (Option.map (fun q : (pSpec₂.FullTranscript × Stmt₃ × Wit₃) × Stmt₃ =>
        ((tr₁ ++ₜ q.1.1, q.1.2.1, q.1.2.2), q.2))) <$>
        (liftM ((Reduction.run s₂ w₂ R₂).run) : Comp oSpec pSpec₁ pSpec₂ _)
      = (do
          let y ← (liftM (Prover.run s₂ w₂ R₂.prover) : Comp oSpec pSpec₁ pSpec₂ _)
          let o₃ ← (liftM (R₂.verifier.verify s₂ y.1).run : Comp oSpec pSpec₁ pSpec₂ _)
          Option.elim o₃ (pure none) fun s₃ =>
            pure (some ((tr₁ ++ₜ y.1, y.2.1, y.2.2), s₃))) := by
  rw [run_run_flat]
  simp only [liftM_bind, Prover.liftM_liftM_base_right, map_bind]
  refine bind_congr fun y => bind_congr fun o => ?_
  cases o <;> simp

end Recognise

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

/-- **Restricting the challenge oracle, right component.** The mirror of
`evalDist_simulateQ_liftM_left`: a computation of the right component is reindexed to
`ChallengeIdx.inr`. -/
lemma evalDist_simulateQ_liftM_right (c : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) α) (s : σ) :
    𝒟[StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
          (liftM c : Comp oSpec pSpec₁ pSpec₂ α)) s]
      = 𝒟[StateT.run (simulateQ (pImplOf pSpec₂ impl) c) s] := by
  induction c using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t oa ih =>
    rw [liftM_bind]
    simp only [simulateQ_bind, StateT.run_bind, evalDist_bind]
    have hhead : 𝒟[StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
          (liftM (liftM (OracleSpec.query t) :
            OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _) : Comp oSpec pSpec₁ pSpec₂ _)) s]
        = 𝒟[StateT.run (simulateQ (pImplOf pSpec₂ impl)
            (liftM (OracleSpec.query t) : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)) s] := by
      rcases t with t | t
      · rfl
      · obtain ⟨i, q⟩ := t
        conv_lhs => rw [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_query]
        have hkey := evalDist_cast_map_uniformSample (challenge_append_inr (pSpec₁ := pSpec₁) i)
        rw [evalDist_map] at hkey
        have hfin : (fun a => (cast (challenge_append_inr (pSpec₁ := pSpec₁) i) a, s)) <$>
              𝒟[($ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i)))]
            = (fun a => (a, s)) <$> 𝒟[($ᵗ (pSpec₂.Challenge i))] := by
          rw [← hkey, Functor.map_map]
        simp [pImplOf, simulateQ_liftM_query, OracleSpec.query]
        exact hfin
    rw [hhead]
    exact bind_congr fun p => ih p.1 p.2


/-- **The swap.** `Reduction.append` runs `P₂` before `V₁`; `R₁` then `R₂` runs `V₁` before
`P₂`. Both read only what `P₁` produced -- `P₂` its output context, `V₁` its transcript -- and
neither reads the other, so a commutative handler cannot tell the two orders apart.

This is the step `AppendCounterexample.lean` shows is false without `IsCommutative`: there the
handler reports the order it was called in, `V₁` sees the state `P₂` left, and the appended
reduction rejects with probability one. -/
theorem evalDist_append_run_swapped
    (hcomm : (pImplOf (pSpec₁ ++ₚ pSpec₂) impl).IsCommutative)
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) (stmt : Stmt₁) (wit : Wit₁) (s : σ) :
    𝒟[StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
        (Reduction.run stmt wit (R₁.append R₂)).run) s]
      = 𝒟[StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl) (do
          let x ← (liftM (Prover.run stmt wit R₁.prover) : Comp oSpec pSpec₁ pSpec₂ _)
          let o₂ ← (liftM (R₁.verifier.verify stmt x.1).run : Comp oSpec pSpec₁ pSpec₂ _)
          let y ← (liftM (Prover.run x.2.1 x.2.2 R₂.prover) : Comp oSpec pSpec₁ pSpec₂ _)
          Option.elim o₂ (pure none) fun s₂ => do
            let o₃ ← (liftM (R₂.verifier.verify s₂ y.1).run : Comp oSpec pSpec₁ pSpec₂ _)
            Option.elim o₃ (pure none) fun s₃ =>
              pure (some ((x.1 ++ₜ y.1, y.2.1, y.2.2), s₃)))) s] := by
  rw [append_run_run_split]
  exact hcomm.bind_prefix _ _ _ _ s

end ChallengeRestrict

section Phases

variable {σ : Type} [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]
  {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **The first phase of the swapped appended run:** `P₁` then `V₁`, keeping both the prover's
output context and the verifier's (possibly failing) output statement. Keeping the pair rather
than collapsing to an `Option` is what lets the second phase still see `P₁`'s transcript. -/
def appendPhase₁ (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁) (stmt : Stmt₁) (wit : Wit₁) :
    Comp oSpec pSpec₁ pSpec₂ ((pSpec₁.FullTranscript × Stmt₂ × Wit₂) × Option Stmt₂) := do
  let x ← (liftM (Prover.run stmt wit R₁.prover) : Comp oSpec pSpec₁ pSpec₂ _)
  let o₂ ← (liftM (R₁.verifier.verify stmt x.1).run : Comp oSpec pSpec₁ pSpec₂ _)
  pure (x, o₂)

/-- **The second phase of the swapped appended run:** `P₂` then `V₂`, on the first phase's
output. `P₂` runs whatever `V₁` returned -- that is what the appended reduction does, and the
completeness bound only needs the branch where `V₁` accepted. -/
def appendPhase₂ (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (p : (pSpec₁.FullTranscript × Stmt₂ × Wit₂) × Option Stmt₂) :
    Comp oSpec pSpec₁ pSpec₂
      (Option (((pSpec₁ ++ₚ pSpec₂).FullTranscript × Stmt₃ × Wit₃) × Stmt₃)) := do
  let y ← (liftM (Prover.run p.1.2.1 p.1.2.2 R₂.prover) : Comp oSpec pSpec₁ pSpec₂ _)
  Option.elim p.2 (pure none) fun s₂ => do
    let o₃ ← (liftM (R₂.verifier.verify s₂ y.1).run : Comp oSpec pSpec₁ pSpec₂ _)
    Option.elim o₃ (pure none) fun s₃ => pure (some ((p.1.1 ++ₜ y.1, y.2.1, y.2.2), s₃))

/-- **The appended run as two phases.** The swap of `evalDist_append_run_swapped`, with the
result split at the point where `R₁` ends and `R₂` begins -- the shape
`OracleComp.one_sub_le_probEvent_bind` consumes. -/
theorem evalDist_append_run_phases
    (hcomm : (pImplOf (pSpec₁ ++ₚ pSpec₂) impl).IsCommutative)
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) (stmt : Stmt₁) (wit : Wit₁) (s : σ) :
    𝒟[StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
        (Reduction.run stmt wit (R₁.append R₂)).run) s]
      = 𝒟[StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
              (appendPhase₁ R₁ stmt wit)) s >>= fun p =>
            StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
              (appendPhase₂ R₂ p.1)) p.2] := by
  have hsplit : (appendPhase₁ R₁ stmt wit >>= appendPhase₂ R₂) = (do
      let x ← (liftM (Prover.run stmt wit R₁.prover) : Comp oSpec pSpec₁ pSpec₂ _)
      let o₂ ← (liftM (R₁.verifier.verify stmt x.1).run : Comp oSpec pSpec₁ pSpec₂ _)
      let y ← (liftM (Prover.run x.2.1 x.2.2 R₂.prover) : Comp oSpec pSpec₁ pSpec₂ _)
      Option.elim o₂ (pure none) fun s₂ => do
        let o₃ ← (liftM (R₂.verifier.verify s₂ y.1).run : Comp oSpec pSpec₁ pSpec₂ _)
        Option.elim o₃ (pure none) fun s₃ =>
          pure (some ((x.1 ++ₜ y.1, y.2.1, y.2.2), s₃))) := by
    simp only [appendPhase₁, appendPhase₂, bind_assoc, pure_bind]
  rw [evalDist_append_run_swapped hcomm, ← hsplit]
  simp only [simulateQ_bind, StateT.run_bind, evalDist_bind]

variable {rel₂ : Set (Stmt₂ × Wit₂)}

/-- `StateT.run'` as a `map` of `StateT.run`, keeping `StateT.run` in the term. Unfolding
`StateT.run'` directly leaves a bare application that the `StateT.run`-shaped lemmas below no
longer match. -/
private lemma stateT_run'_eq {α : Type} (x : StateT σ ProbComp α) (s : σ) :
    StateT.run' x s = (fun p => p.1) <$> StateT.run x s := rfl

/-- Two binds with the same prefix and pointwise-equal continuation events have the same
event probability. -/
private lemma probEvent_bind_congr {α β γ : Type} (mx : ProbComp α) {f : α → ProbComp β}
    {g : α → ProbComp γ} {p : β → Prop} {q : γ → Prop} (h : ∀ a, Pr[ p | f a] = Pr[ q | g a]) :
    Pr[ p | mx >>= f] = Pr[ q | mx >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact congrArg tsum (funext fun a => by rw [h a])

private lemma stateT_run'_map {α β : Type} (f : α → β) (x : StateT σ ProbComp α) (s : σ) :
    StateT.run' (f <$> x) s = f <$> StateT.run' x s := by
  simp only [stateT_run'_eq, StateT.run_map, Functor.map_map]

/-- The state-discarding form of a distributional equality between two simulated runs. -/
private lemma evalDist_stateT_run'_congr {α : Type} {x y : StateT σ ProbComp α} {s : σ}
    (h : 𝒟[StateT.run x s] = 𝒟[StateT.run y s]) : 𝒟[StateT.run' x s] = 𝒟[StateT.run' y s] := by
  rw [stateT_run'_eq, stateT_run'_eq, evalDist_map, evalDist_map, h]

/-- **The first phase's good event is `R₁`'s completeness event.** Left-hand side: `V₁`
accepted, and its output statement is in `rel₂` with `P₁`'s witness and equal to `P₁`'s output
statement. Right-hand side: exactly `Reduction.completeness`'s event for `R₁`. -/
theorem probEvent_appendPhase₁_eq (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (stmt : Stmt₁) (wit : Wit₁) (s : σ) :
    Pr[ fun p : ((pSpec₁.FullTranscript × Stmt₂ × Wit₂) × Option Stmt₂) × σ =>
          Option.elim p.1.2 False fun s₂ => (s₂, p.1.1.2.2) ∈ rel₂ ∧ p.1.1.2.1 = s₂ |
        StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
          (appendPhase₁ R₁ stmt wit)) s]
      = Pr[ fun r : (pSpec₁.FullTranscript × Stmt₂ × Wit₂) × Stmt₂ =>
              (r.2, r.1.2.2) ∈ rel₂ ∧ r.1.2.1 = r.2 |
          OptionT.mk (StateT.run' (simulateQ (pImplOf pSpec₁ impl)
            (Reduction.run stmt wit R₁).run) s)] := by
  rw [OptionT.probEvent_mk, stateT_run'_eq, probEvent_map,
    probEvent_of_evalDist_eq (evalDist_simulateQ_liftM_left (impl := impl) (pSpec₂ := pSpec₂)
      (Reduction.run stmt wit R₁).run s).symm,
    liftM_run_left_eq_map, simulateQ_map, StateT.run_map, probEvent_map]
  unfold appendPhase₁
  refine congrArg _ (funext fun p => ?_)
  rcases hp : p.1.2 with _ | s₂ <;> simp [hp, Function.comp]


variable {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **The second phase's good event is `R₂`'s completeness event.** On the branch where `V₁`
accepted with `s₂` and the prover agreed (`hx`), the second phase is `R₂.run s₂` -- with `P₁`'s
transcript prepended to the output, which the event does not look at. -/
theorem probEvent_appendPhase₂_eq (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (x : pSpec₁.FullTranscript × Stmt₂ × Wit₂) (s₂ : Stmt₂) (hx : x.2.1 = s₂) (s₁ : σ) :
    Pr[ fun o : Option (((pSpec₁ ++ₚ pSpec₂).FullTranscript × Stmt₃ × Wit₃) × Stmt₃) =>
          Option.elim o False fun r => (r.2, r.1.2.2) ∈ rel₃ ∧ r.1.2.1 = r.2 |
        StateT.run' (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
          (appendPhase₂ R₂ (x, some s₂))) s₁]
      = Pr[ fun r : (pSpec₂.FullTranscript × Stmt₃ × Wit₃) × Stmt₃ =>
              (r.2, r.1.2.2) ∈ rel₃ ∧ r.1.2.1 = r.2 |
          OptionT.mk (StateT.run' (simulateQ (pImplOf pSpec₂ impl)
            (Reduction.run s₂ x.2.2 R₂).run) s₁)] := by
  have hphase : appendPhase₂ R₂ (x, some s₂)
      = (Option.map (fun q : (pSpec₂.FullTranscript × Stmt₃ × Wit₃) × Stmt₃ =>
            ((x.1 ++ₜ q.1.1, q.1.2.1, q.1.2.2), q.2))) <$>
          (liftM ((Reduction.run s₂ x.2.2 R₂).run) : Comp oSpec pSpec₁ pSpec₂ _) := by
    rw [liftM_run_right_eq_map]
    simp only [appendPhase₂, hx, Option.elim]
  rw [hphase, simulateQ_map, stateT_run'_map, probEvent_map, OptionT.probEvent_mk,
    probEvent_of_evalDist_eq (evalDist_stateT_run'_congr
      (evalDist_simulateQ_liftM_right (impl := impl) (pSpec₁ := pSpec₁)
        (Reduction.run s₂ x.2.2 R₂).run s₁))]
  refine congrArg _ (funext fun o => ?_)
  cases o <;> simp [Function.comp]


variable {rel₁ : Set (Stmt₁ × Wit₁)} (init : ProbComp σ)

open scoped NNReal in
/-- **Sequential composition preserves completeness.**

Two hypotheses beyond the original statement, both forced and both exhibited as necessary:

* `hcomm` -- the handler answers queries commutatively. `Reduction.append` runs `P₁, P₂, V₁,
  V₂` while `R₁` then `R₂` runs `P₁, V₁, P₂, V₂`, and `AppendCounterexample.lean` gives two
  perfectly complete reductions whose append rejects with probability one under a handler that
  reports the order it was called in.
* `h₂` at every initial state -- `R₂` starts from whatever state `R₁` left behind, not from a
  fresh `init`. Commutativity says the two *orders* agree; it says nothing about `R₂` run from
  a state `R₁` has already written to.

Both are free when the handler is stateless (`QueryImpl.IsStateless`), which is the case at
`oSpec = []ₒ`; see `append_completeness_of_isStateless`. -/
theorem append_completeness'
    (hcomm : (pImplOf (pSpec₁ ++ₚ pSpec₂) impl).IsCommutative)
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) {ε₁ ε₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ ε₁)
    (h₂ : ∀ s : σ, R₂.completeness (pure s) impl rel₂ rel₃ ε₂) :
      (R₁.append R₂).completeness init impl rel₁ rel₃ (ε₁ + ε₂) := by
  intro stmtIn witIn hRelIn
  dsimp only
  rw [ge_iff_le, OptionT.probEvent_mk]
  have hphases : ∀ s₀ : σ, 𝒟[StateT.run' (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
        (Reduction.run stmtIn witIn (R₁.append R₂)).run) s₀]
      = 𝒟[StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
              (appendPhase₁ R₁ stmtIn witIn)) s₀ >>= fun p =>
            StateT.run' (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
              (appendPhase₂ R₂ p.1)) p.2] := by
    intro s₀
    rw [stateT_run'_eq, evalDist_map, evalDist_append_run_phases hcomm]
    simp only [stateT_run'_eq, evalDist_bind, evalDist_map, map_bind]
  have hbind : 𝒟[init >>= fun s₀ =>
        StateT.run' (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
          (Reduction.run stmtIn witIn (R₁.append R₂)).run) s₀]
      = 𝒟[(init >>= fun s₀ =>
            StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
              (appendPhase₁ R₁ stmtIn witIn)) s₀) >>= fun p =>
            StateT.run' (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
              (appendPhase₂ R₂ p.1)) p.2] := by
    simp only [evalDist_bind, bind_assoc]
    exact bind_congr fun s₀ => by rw [hphases s₀, evalDist_bind]
  rw [probEvent_of_evalDist_eq hbind, ENNReal.coe_add]
  refine one_sub_le_probEvent_bind (P := fun p => Option.elim p.1.2 False
      fun s₂ => (s₂, p.1.1.2.2) ∈ rel₂ ∧ p.1.1.2.1 = s₂) ?_ ?_
  · have hcomp := h₁ stmtIn witIn hRelIn
    dsimp only at hcomp
    rw [ge_iff_le, OptionT.probEvent_mk] at hcomp
    refine le_trans hcomp (le_of_eq ?_)
    exact (probEvent_bind_congr init fun s₀ =>
      (probEvent_appendPhase₁_eq R₁ stmtIn witIn s₀).trans (OptionT.probEvent_mk _ _)).symm
  · rintro ⟨⟨x, (_ | s₂)⟩, s₁⟩ hp
    · exact absurd hp id
    · obtain ⟨hrel, hprv⟩ := hp
      have hc := h₂ s₁ s₂ x.2.2 hrel
      dsimp only at hc
      rw [ge_iff_le, OptionT.probEvent_mk] at hc
      rw [probEvent_appendPhase₂_eq R₂ x s₂ hprv s₁, OptionT.probEvent_mk]
      simpa using hc

end Phases



end Reduction
