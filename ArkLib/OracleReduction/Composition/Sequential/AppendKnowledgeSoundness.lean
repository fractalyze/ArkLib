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
