/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendSoundness
import ArkLib.OracleReduction.EagerChallenges
import ArkLib.OracleReduction.ProverContext
import ArkLib.OracleReduction.Security.RandomizedAdversary

/-!
# Sequential composition of knowledge soundness

Plain soundness composes by splitting the adversary in two and bounding each half
(`AppendSoundness.lean`). Knowledge soundness cannot: the first component's game fixes the
adversary's output witness type to `Wit₂`, and the only source of a `Wit₂` is "run the second half,
then run `E₂`". A `Prover oSpec …` has no randomness of its own, so it cannot draw the second
half's challenges.

The way through is to hardwire them. For a fixed challenge vector `c`, running the second half is
an ordinary `oSpec` computation (`Prover.runFixed`), so the first-half adversary below is a legal
prover; `Verifier.knowledgeSoundnessWith_randomized` then averages `c` away, and
`Prover.evalDist_run_drawFirst` says that average is the appended run.

`Prover.withContext` supplies the input statement and the first half's transcript to the output
step, which needs both to re-derive the intermediate statement.
-/

open OracleComp OracleSpec ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {m n : ℕ}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

namespace Prover

/-- **The first half of an adversary, made to output an intermediate witness.**

It runs `P`'s first `m` rounds, and then -- in its output step, where only `oSpec` is available --
runs `P`'s remaining rounds with the challenges taken from `c`, re-derives the intermediate
statement from the input statement and the transcript it kept, and hands both to `E₂`.

`stmtOut` is the statement it reports; nothing reads it, since the knowledge-soundness event reads
the *verifier*'s output. `junk` is what it outputs when `E₂` fails, on a branch the bound does not
look at. -/
def takeLeftExtract (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (c : pSpec₂.ChalsBelow n) (stmtOut : Stmt₂) (junk : Wit₂) :
    Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁ :=
  (P.takeLeft stmtOut).withContext fun stmt₁ tr₁ cut => do
    let y ← (P.dropLeft (Stmt₂ := Stmt₂)).runFixed c stmtOut
              (cast (Prover.prvState_cut_eq P) cut)
    let w? ← (E₂ (verify stmt₁ tr₁) y.2.2 y.1 [] []).run
    return (stmtOut, w?.getD junk)

/-- Running the extracting adversary: the first half's run, then the hardwired second half, then
`E₂`. Just `withContext_run` at this instance, recorded because every step of the composition
argument starts from it. -/
theorem takeLeftExtract_run (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (c : pSpec₂.ChalsBelow n) (stmtOut : Stmt₂) (junk : Wit₂) (stmt : Stmt₁) (wit : Wit₁) :
    (P.takeLeftExtract verify E₂ c stmtOut junk).run stmt wit = (do
      let p ← (P.takeLeft stmtOut).run stmt wit
      let r ← (liftM (do
        let y ← (P.dropLeft (Stmt₂ := Stmt₂)).runFixed c stmtOut
                  (cast (Prover.prvState_cut_eq P) p.2.2)
        let w? ← (E₂ (verify stmt p.1) y.2.2 y.1 [] []).run
        return (stmtOut, w?.getD junk)) :
          OracleComp (oSpec + [pSpec₁.Challenge]ₒ) (Stmt₂ × Wit₂))
      return (p.1, r)) :=
  withContext_run _ _ stmt wit

end Prover

namespace Extractor.Straightline

variable {StmtIn WitIn WitOut : Type} {N : ℕ} {pSpec : ProtocolSpec N}

/-- **An extractor that does not read the query logs.**

The composition below needs this of both components. The first component's adversary has to call
`E₂` from inside its `output` step, where the appended game's logs are not visible; and the
composed extractor has to call `E₁` with what the first component's game would have logged, which
it cannot reconstruct for the verifier (the appended verifier's log interleaves `V₁`'s with `V₂`'s
and nothing records the split).

At `oSpec = []ₒ` -- where every protocol in this library instantiates -- there is nothing to log
and the condition is vacuous. Lifting it in general means giving the knowledge-soundness game a
per-phase log rather than one flat `QueryLog`. -/
def IsLogIndependent (E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec) : Prop :=
  ∀ stmtIn witOut tr l₁ l₂ l₁' l₂', E stmtIn witOut tr l₁ l₂ = E stmtIn witOut tr l₁' l₂'

/-- **The composed straightline extractor**, for a deterministic first verifier and log-blind
components. Given the final witness it re-derives the intermediate statement from the transcript,
extracts an intermediate witness with `E₂`, and feeds that to `E₁`.

`Extractor.Straightline.append` in `Append.lean` is the same shape with `V₁.verify` in place of
`verify` and the game's logs threaded through. This variant exists because the composition proof
needs the intermediate statement to be a *function* of the transcript -- the first component's
adversary has to re-derive it inside its own `output` step, where re-running a randomized `V₁`
would draw fresh randomness -- and needs the logs gone. -/
def appendDet (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂) :
    Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂) :=
  fun stmt₁ wit₃ transcript _ _ => do
    let wit₂ ← E₂ (verify stmt₁ transcript.fst) wit₃ transcript.snd [] []
    E₁ stmt₁ wit₂ transcript.fst [] []

/-- The composed extractor reads no log, whatever its components do. -/
theorem appendDet_isLogIndependent (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂) :
    (appendDet verify E₁ E₂).IsLogIndependent := fun _ _ _ _ _ _ _ => rfl

end Extractor.Straightline

namespace Verifier

variable {StmtIn WitIn StmtOut WitOut : Type} {N : ℕ} {pSpec : ProtocolSpec N}

/-- **The knowledge-soundness game, with the logs gone.** For a log-independent extractor the game
only ever *produces* its logs, so the whole run can be taken log-free -- which is what puts it
back in reach of the `Reduction.run` machinery the soundness composition is built on. -/
theorem exec_eq_of_logIndependent
    {E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec} (hE : E.IsLogIndependent)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmtIn : StmtIn) (witIn : WitIn) :
    ((Reduction.mk P V).runWithLog stmtIn witIn >>= fun r =>
        liftM (E stmtIn r.1.1.2.2 r.1.1.1 r.2.1.fst r.2.2).run >>= fun w? =>
          (pure (stmtIn, w?, r.1.2, r.1.1.2.2) :
            OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) _))
      = ((Reduction.mk P V).run stmtIn witIn >>= fun r =>
          liftM (E stmtIn r.1.2.2 r.1.1 [] []).run >>= fun w? =>
            (pure (stmtIn, w?, r.2, r.1.2.2) :
              OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) _)) := by
  let cont : ((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut) →
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (StmtIn × Option WitIn × StmtOut × WitOut) :=
    fun r => liftM (E stmtIn r.1.2.2 r.1.1 [] []).run >>= fun w? =>
      pure (stmtIn, w?, r.2, r.1.2.2)
  have h1 : ((Reduction.mk P V).runWithLog stmtIn witIn >>= fun r =>
        liftM (E stmtIn r.1.1.2.2 r.1.1.1 r.2.1.fst r.2.2).run >>= fun w? =>
          (pure (stmtIn, w?, r.1.2, r.1.1.2.2) :
            OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) _))
      = ((Reduction.mk P V).runWithLog stmtIn witIn >>= fun r => cont r.1) :=
    bind_congr fun r => by
      rw [show cont r.1 = liftM (E stmtIn r.1.1.2.2 r.1.1.1 [] []).run >>= fun w? =>
            (pure (stmtIn, w?, r.1.2, r.1.1.2.2) :
              OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) _) from rfl,
        hE stmtIn r.1.1.2.2 r.1.1.1 r.2.1.fst r.2.2 [] []]
  have h2 : ((Reduction.mk P V).runWithLog stmtIn witIn >>= fun r => cont r.1)
      = (Prod.fst <$> (Reduction.mk P V).runWithLog stmtIn witIn) >>= cont :=
    (bind_map_left _ _ _).symm
  rw [h1, h2, Reduction.runWithLog_discard_logs_eq_run]

end Verifier
