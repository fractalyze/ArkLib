/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Execution

/-!
# A prover that remembers its own context

`Prover.output` sees only the prover's private state, so a prover whose final step needs the input
statement or the transcript has to carry them itself. `Prover.withContext` does that: it runs an
existing prover, threading the input statement and the transcript so far alongside its state, and
replaces the output step with one that may read them.

The consumer is composing knowledge soundness. There the first component's adversary has to output
an intermediate witness obtained by re-deriving the intermediate statement from the input statement
and the first half's transcript, and then running the second component's extractor.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {N : ℕ} {pSpec : ProtocolSpec N}
  {S W S' W' S'' W'' : Type}

/-- Run `P₀`, remembering the input statement and the transcript, and finish with `out` -- which
sees both, along with `P₀`'s output witness. -/
def withContext (P₀ : Prover oSpec S W S' W' pSpec)
    (out : S → pSpec.FullTranscript → W' → OracleComp oSpec (S'' × W'')) :
    Prover oSpec S W S'' W'' pSpec where
  PrvState i := S × pSpec.Transcript i × P₀.PrvState i
  input ctx := (ctx.1, default, P₀.input ctx)
  sendMessage i st := do
    let r ← P₀.sendMessage i st.2.2
    return (r.1, (st.1, st.2.1.concat r.1, r.2))
  receiveChallenge i st := do
    let f ← P₀.receiveChallenge i st.2.2
    return fun ch => (st.1, st.2.1.concat ch, f ch)
  output st := do
    let o ← P₀.output st.2.2
    out st.1 st.2.1 o.2

variable (P₀ : Prover oSpec S W S' W' pSpec)
  (out : S → pSpec.FullTranscript → W' → OracleComp oSpec (S'' × W''))

/-- The added context is exactly what the run already produces, so a partial run of the augmented
prover is a partial run of the original with the statement and transcript copied alongside. -/
theorem withContext_runToRound (stmt : S) (wit : W) :
    ∀ (v : ℕ) (hv : v ≤ N),
      (P₀.withContext out).runToRound ⟨v, by omega⟩ stmt wit
        = (fun p => (p.1, (stmt, p.1, p.2))) <$> P₀.runToRound ⟨v, by omega⟩ stmt wit := by
  intro v
  induction v with
  | zero =>
    intro _
    rw [runToRound_mk_zero, runToRound_mk_zero]
    simp only [Prover.withContext]
    exact congrArg _ (Prod.ext (Subsingleton.elim _ _) rfl)
  | succ v ih =>
    intro hv
    rw [runToRound_mk_succ _ v (by omega), runToRound_mk_succ P₀ v (by omega), ih (by omega)]
    unfold Prover.processRound
    refine Eq.trans (bind_map_left _ _ _) (Eq.trans ?_ (map_bind _ _ _).symm)
    refine bind_congr fun p => ?_
    obtain ⟨transcript, state⟩ := p
    dsimp only
    split
    · simp only [Prover.withContext, liftM_map, bind_map_left, bind_pure_comp]
      refine Eq.trans ?_ (map_bind _ _ _).symm
      refine bind_congr fun _ => ?_
      symm
      exact Functor.map_map _ _ _
    · simp only [Prover.withContext, liftM_map, bind_pure_comp, Functor.map_map]
      symm
      exact Functor.map_map _ _ _

/-- Running the augmented prover is running the original and then `out`, on the transcript the run
produced. -/
theorem withContext_run (stmt : S) (wit : W) :
    (P₀.withContext out).run stmt wit = (do
      let p ← P₀.run stmt wit
      let r ← (liftM (out stmt p.1 p.2.2) :
        OracleComp (oSpec + [pSpec.Challenge]ₒ) (S'' × W''))
      return (p.1, r)) := by
  unfold Prover.run
  rw [runToRound_last, runToRound_last, withContext_runToRound P₀ out stmt wit N le_rfl]
  simp only [Prover.withContext, map_bind, bind_map_left, liftM_bind, bind_assoc, bind_pure_comp]
  exact bind_map_left _ _ _

end Prover
