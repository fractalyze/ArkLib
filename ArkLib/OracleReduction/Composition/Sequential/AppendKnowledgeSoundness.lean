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

/-- The knowledge-soundness game's run, for a log-blind extractor: no logs, and the reduction run
in its ordinary (`Reduction.run`) form. -/
def ksExec (E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmtIn : StmtIn) (witIn : WitIn) :
    OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
      (StmtIn × Option WitIn × StmtOut × WitOut) :=
  (Reduction.mk P V).run stmtIn witIn >>= fun r =>
    liftM (E stmtIn r.1.2.2 r.1.1 [] []).run >>= fun w? => pure (stmtIn, w?, r.2, r.1.2.2)

/-- The knowledge-soundness bad event: the extractor failed to produce a witness for the input
relation, while the run's own output was a valid pair for the output relation. -/
def ksBad (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) :
    StmtIn × Option WitIn × StmtOut × WitOut → Prop :=
  fun p => (∀ w ∈ p.2.1, (p.1, w) ∉ relIn) ∧ (p.2.2.1, p.2.2.2) ∈ relOut

/-- The log-free game, with the reduction's failure bookkeeping pulled out into one
`Option.elim`. The extractor's lift is a composite one; `monadLift_liftM_OptionT` is what puts it
in the two-step form the `OptionT.run` lemmas match. -/
theorem ksExec_run_eq (E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmtIn : StmtIn) (witIn : WitIn) :
    (ksExec E V P stmtIn witIn).run
      = ((Reduction.mk P V).run stmtIn witIn).run >>= fun o =>
          Option.elim o (pure none) fun r =>
            (liftM (E stmtIn r.1.2.2 r.1.1 [] []).run :
                OracleComp (oSpec + [pSpec.Challenge]ₒ) _) >>= fun w? =>
              pure (some (stmtIn, w?, r.2, r.1.2.2)) := by
  unfold ksExec
  rw [OptionT.run_bind]
  refine bind_congr fun o => ?_
  cases o with
  | none => simp [Option.elimM]
  | some r =>
    simp only [Option.elimM, Option.elim, ← monadLift_liftM_OptionT]
    exact Eq.trans (OptionT.run_liftM_bind _ _) (bind_congr fun w? => OptionT.run_pure _)

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
      = ksExec E V P stmtIn witIn := by
  let cont : ((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut) →
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        (StmtIn × Option WitIn × StmtOut × WitOut) :=
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
  rfl

open scoped NNReal in
/-- Knowledge soundness for a log-blind extractor, restated on the log-free game. -/
theorem knowledgeSoundnessWith_iff_ksExec [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {V : Verifier oSpec StmtIn StmtOut pSpec}
    {E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec} (hE : E.IsLogIndependent)
    {ε : ℝ≥0} :
    V.knowledgeSoundnessWith init impl relIn relOut E ε
      ↔ ∀ (stmtIn : StmtIn) (witIn : WitIn)
          (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec),
          Pr[ ksBad relIn relOut | OptionT.mk (init >>= fun s =>
            StateT.run' (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
                QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
              (ksExec E V P stmtIn witIn).run) s)] ≤ ε := by
  unfold Verifier.knowledgeSoundnessWith
  refine forall_congr' fun stmtIn => forall_congr' fun witIn => forall_congr' fun P => ?_
  dsimp only
  rw [exec_eq_of_logIndependent hE]
  rfl

end Verifier

section Compose

namespace Verifier

/-- The appended game, instrumented with the intermediate statement and the witness `E₂` extracted.
Neither is in the game's own output, and the union bound splits on both, so they are carried along
and projected away afterwards. -/
def ksExecInstr (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtIn : Stmt₁) (witIn : Wit₁) :
    OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
      ((Stmt₁ × Option Wit₁ × Stmt₃ × Wit₃) × Stmt₂ × Option Wit₂) :=
  (Reduction.mk P (V₁.append V₂)).run stmtIn witIn >>= fun r =>
    (liftM ((liftM (E₂ (verify stmtIn r.1.1.fst) r.1.2.2 r.1.1.snd [] []).run :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) :
        OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) _) >>= fun w₂? =>
      (liftM ((liftM (w₂?.elim (pure none) fun w₂ => (E₁ stmtIn w₂ r.1.1.fst [] []).run) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) :
          OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) _) >>= fun w₁? =>
        pure ((stmtIn, w₁?, r.2, r.1.2.2), verify stmtIn r.1.1.fst, w₂?)

/-- The game is the instrumented game with the instrumentation forgotten. -/
theorem ksExec_appendDet_eq (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtIn : Stmt₁) (witIn : Wit₁) :
    ksExec (Extractor.Straightline.appendDet verify E₁ E₂) (V₁.append V₂) P stmtIn witIn
      = Prod.fst <$> ksExecInstr verify E₁ E₂ V₁ V₂ P stmtIn witIn := by
  unfold ksExec ksExecInstr Extractor.Straightline.appendDet
  rw [map_bind]
  refine bind_congr fun r => ?_
  simp only [OptionT.run_bind, Option.elimM, liftM_bind, bind_assoc, map_bind, map_pure,
    monadLift_liftM_OptionT]

/-- The two extractors and the packaging, run on the reduction's (possibly failing) result. -/
def ksExtractTail (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂) (stmtIn : Stmt₁)
    (o : Option (((pSpec₁ ++ₚ pSpec₂).FullTranscript × Stmt₃ × Wit₃) × Stmt₃)) :
    OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (Option ((Stmt₁ × Option Wit₁ × Stmt₃ × Wit₃) × Stmt₂ × Option Wit₂)) :=
  Option.elim o (pure none) fun r =>
    liftM (E₂ (verify stmtIn r.1.1.fst) r.1.2.2 r.1.1.snd [] []).run >>= fun w₂? =>
      liftM (w₂?.elim (pure none) fun w₂ => (E₁ stmtIn w₂ r.1.1.fst [] []).run) >>= fun w₁? =>
        pure (some ((stmtIn, w₁?, r.2, r.1.2.2), verify stmtIn r.1.1.fst, w₂?))

/-- Everything the instrumented game does after the cut: the second half's phase, then the
extractors. -/
def ksTail (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (stmtOut : Stmt₂)
    (stmtIn : Stmt₁)
    (p : (pSpec₁.FullTranscript × Stmt₂ × Reduction.CutState P) × Option Stmt₂) :
    OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (Option ((Stmt₁ × Option Wit₁ × Stmt₃ × Wit₃) × Stmt₂ × Option Wit₂)) :=
  Reduction.soundPhase₂ P V₂ stmtOut p >>= ksExtractTail verify E₁ E₂ stmtIn

/-- The instrumented game is the appended run followed by the extractor tail. -/
theorem ksExecInstr_run_eq (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtIn : Stmt₁) (witIn : Wit₁) :
    (ksExecInstr verify E₁ E₂ V₁ V₂ P stmtIn witIn).run
      = ((Reduction.mk P (V₁.append V₂)).run stmtIn witIn).run
          >>= ksExtractTail verify E₁ E₂ stmtIn := by
  unfold ksExecInstr ksExtractTail
  rw [OptionT.run_bind]
  refine bind_congr fun o => ?_
  cases o with
  | none => simp [Option.elimM]
  | some r =>
    simp only [Option.elimM, Option.elim]
    refine Eq.trans (OptionT.run_liftM_bind _ _) (bind_congr fun w₂? => ?_)
    exact OptionT.run_liftM_bind _ _

/-- The post-cut tail as a computation of the *second* protocol's spec: the second reduction's
run, then both extractors. Everything after the cut only ever queries `oSpec` and `pSpec₂`'s
challenges, so it factors through that spec -- which is what lets
`Reduction.evalDist_simulateQ_liftM_right` hand it to the second component's handler. -/
def ksTailRight (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (stmtIn : Stmt₁)
    (x : pSpec₁.FullTranscript × Stmt₂ × Reduction.CutState P) (s₂ : Stmt₂) :
    OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
      (Option ((Stmt₁ × Option Wit₁ × Stmt₃ × Wit₃) × Stmt₂ × Option Wit₂)) :=
  ((Reduction.run s₂ (cast (Prover.prvState_cut_eq P) x.2.2)
      (Reduction.mk (P.dropLeft (Stmt₂ := Stmt₂)) V₂)).run) >>= fun o =>
    Option.elim o (pure none) fun q =>
      liftM (E₂ s₂ q.1.2.2 q.1.1 [] []).run >>= fun w₂? =>
        liftM (w₂?.elim (pure none) fun w₂ => (E₁ stmtIn w₂ x.1 [] []).run) >>= fun w₁? =>
          pure (some ((stmtIn, w₁?, q.2, q.1.2.2), s₂, w₂?))

/-- Running the second component's reduction against the state-baked second half is running it
against `dropLeft` from that state. -/
theorem run_mk_dropLeftFrom (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (w : P.PrvState (Prover.rightIdx m (0 : Fin (n + 1))))
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) (s₂ : Stmt₂) (wit : Wit₂) :
    Reduction.run s₂ wit (Reduction.mk (Prover.dropLeftFrom P w) V₂)
      = Reduction.run s₂ w (Reduction.mk (P.dropLeft (Stmt₂ := Stmt₂)) V₂) := rfl

/-- Everything the post-cut tail does *after* the adversary's second half has run: the second
verifier, then both extractors. Only `oSpec` is queried from here on. -/
def ksTailAfterProver (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (stmtIn : Stmt₁)
    (x : pSpec₁.FullTranscript × Stmt₂ × Reduction.CutState P) (s₂ : Stmt₂)
    (y : pSpec₂.FullTranscript × Stmt₃ × Wit₃) :
    OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
      (Option ((Stmt₁ × Option Wit₁ × Stmt₃ × Wit₃) × Stmt₂ × Option Wit₂)) :=
  liftM (V₂.verify s₂ y.1).run >>= fun o₃ =>
    Option.elim o₃ (pure none) fun s₃ =>
      liftM (E₂ s₂ y.2.2 y.1 [] []).run >>= fun w₂? =>
        liftM (w₂?.elim (pure none) fun w₂ => (E₁ stmtIn w₂ x.1 [] []).run) >>= fun w₁? =>
          pure (some ((stmtIn, w₁?, s₃, y.2.2), s₂, w₂?))

/-- The post-cut tail is the adversary's second half, then everything else. -/
theorem ksTailRight_eq_bind (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (stmtIn : Stmt₁)
    (x : pSpec₁.FullTranscript × Stmt₂ × Reduction.CutState P) (s₂ : Stmt₂) :
    ksTailRight verify E₁ E₂ V₂ P stmtIn x s₂
      = Prover.run s₂ (cast (Prover.prvState_cut_eq P) x.2.2) (P.dropLeft (Stmt₂ := Stmt₂))
          >>= ksTailAfterProver verify E₁ E₂ V₂ P stmtIn x s₂ := by
  rw [ksTailRight, Reduction.run_run_flat, bind_assoc]
  refine bind_congr fun y => ?_
  rw [ksTailAfterProver, bind_assoc]
  refine bind_congr fun o₃ => ?_
  cases o₃ <;> simp

open scoped NNReal in
/-- **The second half's challenges, drawn before the tail.** `Prover.evalDist_run_drawFirst`
applied to the adversary's second half where it sits, at the front of the post-cut tail. With the
challenges in hand, that half is an ordinary `oSpec` computation. -/
theorem evalDist_ksTailRight_drawFirst [∀ i, SampleableType (pSpec₂.Challenge i)]
    (implP : QueryImpl oSpec ProbComp) (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (stmtIn : Stmt₁)
    (x : pSpec₁.FullTranscript × Stmt₂ × Reduction.CutState P) (s₂ : Stmt₂) :
    𝒟[simulateQ (implP.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec₂.Challenge]ₒ) ProbComp)
        (ksTailRight verify E₁ E₂ V₂ P stmtIn x s₂)]
      = 𝒟[pSpec₂.drawChalsBelow n le_rfl >>= fun c =>
          simulateQ (implP.addLift challengeQueryImpl :
              QueryImpl (oSpec + [pSpec₂.Challenge]ₒ) ProbComp)
            ((liftM ((P.dropLeft (Stmt₂ := Stmt₂)).runFixed c s₂
                (cast (Prover.prvState_cut_eq P) x.2.2)) :
                OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)
              >>= ksTailAfterProver verify E₁ E₂ V₂ P stmtIn x s₂)] := by
  have hD : 𝒟[simulateQ (implP.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec₂.Challenge]ₒ) ProbComp)
        (Prover.run s₂ (cast (Prover.prvState_cut_eq P) x.2.2) (P.dropLeft (Stmt₂ := Stmt₂)))]
      = 𝒟[pSpec₂.drawChalsBelow n le_rfl >>= fun c =>
          simulateQ (implP.addLift challengeQueryImpl :
              QueryImpl (oSpec + [pSpec₂.Challenge]ₒ) ProbComp)
            ((liftM ((P.dropLeft (Stmt₂ := Stmt₂)).runFixed c s₂
                (cast (Prover.prvState_cut_eq P) x.2.2)) :
                OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _))] := by
    rw [Prover.evalDist_run_drawFirst implP (P.dropLeft (Stmt₂ := Stmt₂)) s₂ _]
    exact congrArg evalDist (bind_congr fun c =>
      ((Prover.simulateQ_addLift_base implP challengeQueryImpl _).trans
        (Prover.simulateQ_runFixed implP _ c s₂ _)).symm)
  rw [ksTailRight_eq_bind]
  refine Eq.trans (congrArg evalDist (simulateQ_bind _ _ _))
    (Eq.trans (Prover.evalDist_bind_congr_prefix hD _)
      (Eq.trans (congrArg evalDist (bind_assoc _ _ _)) ?_))
  exact congrArg evalDist (bind_congr fun c => (simulateQ_bind _ _ _).symm)

/-- On the branch where the first verifier accepted with `s₂`, the post-cut tail is exactly its
second-protocol form, lifted. -/
theorem ksTail_eq (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (stmtOut : Stmt₂)
    (stmtIn : Stmt₁) (x : pSpec₁.FullTranscript × Stmt₂ × Reduction.CutState P) (s₂ : Stmt₂)
    (hs₂ : s₂ = verify stmtIn x.1) :
    ksTail verify E₁ E₂ V₂ P stmtOut stmtIn (x, some s₂)
      = liftM (ksTailRight verify E₁ E₂ V₂ P stmtIn x s₂) := by
  rw [ksTail, Reduction.soundPhase₂_eq, ksTailRight, liftM_bind, bind_map_left]
  refine bind_congr fun o => ?_
  cases o with
  | none => simp [ksExtractTail]
  | some q =>
    simp only [ksExtractTail, Option.map_some, Option.elim, FullTranscript.append_fst,
      FullTranscript.append_snd, ← hs₂, liftM_bind, Prover.liftM_liftM_base_right, liftM_pure]

variable {σ : Type} [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]
  {impl : QueryImpl oSpec (StateT σ ProbComp)} {init : ProbComp σ}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- **The instrumented game, split at the cut.** The swap of
`Reduction.evalDist_mk_append_run_swapped`, carried through the extractor tail. -/
theorem evalDist_ksExecInstr_split
    (hcomm : (Reduction.pImplOf (pSpec₁ ++ₚ pSpec₂) impl).IsCommutative)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (stmtOut : Stmt₂)
    (stmtIn : Stmt₁) (witIn : Wit₁) (s : σ) :
    𝒟[StateT.run (simulateQ (Reduction.pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
        (ksExecInstr verify E₁ E₂ V₁ V₂ P stmtIn witIn).run) s]
      = 𝒟[StateT.run (simulateQ (Reduction.pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
            (Reduction.soundPhase₁ P V₁ stmtOut stmtIn witIn)) s >>= fun p =>
          StateT.run (simulateQ (Reduction.pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
            (ksTail verify E₁ E₂ V₂ P stmtOut stmtIn p.1)) p.2] := by
  rw [ksExecInstr_run_eq, QueryImpl.evalDist_simulateQ_run_bind,
    Reduction.evalDist_mk_append_run_phases P V₁ V₂ stmtOut hcomm stmtIn witIn s,
    evalDist_bind, evalDist_bind, bind_assoc]
  refine bind_congr fun p => ?_
  rw [ksTail, QueryImpl.evalDist_simulateQ_run_bind]

open scoped NNReal in
/-- **The `ε₂` bound, after the cut.** Everything past the cut is `V₂`'s knowledge-soundness game
against the adversary's second half, with the first extractor appended -- which can only lose mass
and whose result this event does not read. -/
theorem probEvent_ksTailRight_le [Nonempty Wit₂]
    {E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂} (hE₂ : E₂.IsLogIndependent)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (stmtIn : Stmt₁)
    {ε₂ : ℝ≥0} (h₂ : ∀ s : σ, V₂.knowledgeSoundnessWith (pure s) impl rel₂ rel₃ E₂ ε₂)
    (x : pSpec₁.FullTranscript × Stmt₂ × Reduction.CutState P) (s₂ : Stmt₂) (s₁ : σ) :
    Pr[ fun o => Option.elim o False fun p =>
          ksBad rel₂ rel₃ (p.2.1, p.2.2, p.1.2.2.1, p.1.2.2.2)
      | StateT.run' (simulateQ (Reduction.pImplOf pSpec₂ impl)
          (ksTailRight verify E₁ E₂ V₂ P stmtIn x s₂)) s₁] ≤ ε₂ := by
  classical
  have hc := (knowledgeSoundnessWith_iff_ksExec hE₂).mp (h₂ s₁) s₂ (Classical.arbitrary Wit₂)
    (Prover.dropLeftFrom P (cast (Prover.prvState_cut_eq P) x.2.2))
  rw [pure_bind, OptionT.probEvent_mk, ksExec_run_eq, run_mk_dropLeftFrom] at hc
  refine le_trans ?_ hc
  rw [ksTailRight, Reduction.stateT_run'_eq, Reduction.stateT_run'_eq]
  simp only [simulateQ_bind, StateT.run_bind]
  rw [probEvent_map, probEvent_map]
  simp only [Reduction.pImplOf, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun q => mul_le_mul' le_rfl ?_
  cases hq : q.1 with
  | none =>
    simp only [hq, Option.elim, simulateQ_pure, StateT.run_pure]
    rw [probEvent_pure, probEvent_pure]
    simp
  | some r =>
    simp only [hq, Option.elim, simulateQ_bind, StateT.run_bind]
    rw [probEvent_bind_eq_tsum]
    conv_rhs => rw [probEvent_bind_eq_tsum]
    refine ENNReal.tsum_le_tsum fun w => mul_le_mul' le_rfl ?_
    by_cases hb : ksBad rel₂ rel₃ (s₂, w.1, r.2, r.1.2.2)
    · refine le_trans probEvent_le_one (le_of_eq ?_)
      simp only [simulateQ_pure, StateT.run_pure]
      rw [probEvent_pure]
      simp [hb]
    · simp only [← bind_pure_comp, simulateQ_map, StateT.run_map, probEvent_map,
        simulateQ_pure, StateT.run_pure, probEvent_pure, Function.comp, Option.elim]
      simp [hb]

/-- The whole post-cut tail with the second half's challenges hardwired: an `oSpec` computation,
because that is all any of it queries once the challenges are supplied. -/
def ksTailBase (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (stmtIn : Stmt₁)
    (x : pSpec₁.FullTranscript × Stmt₂ × Reduction.CutState P) (s₂ : Stmt₂)
    (c : pSpec₂.ChalsBelow n) :
    OracleComp oSpec (Option ((Stmt₁ × Option Wit₁ × Stmt₃ × Wit₃) × Stmt₂ × Option Wit₂)) :=
  (P.dropLeft (Stmt₂ := Stmt₂)).runFixed c s₂ (cast (Prover.prvState_cut_eq P) x.2.2)
    >>= fun y => (V₂.verify s₂ y.1).run >>= fun o₃ =>
      Option.elim o₃ (pure none) fun s₃ =>
        (E₂ s₂ y.2.2 y.1 [] []).run >>= fun w₂? =>
          (w₂?.elim (pure none) fun w₂ => (E₁ stmtIn w₂ x.1 [] []).run) >>= fun w₁? =>
            pure (some ((stmtIn, w₁?, s₃, y.2.2), s₂, w₂?))

/-- With the challenges hardwired, the post-cut tail is a lifted `oSpec` computation. -/
theorem ksTailAfterProver_eq_base (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (stmtIn : Stmt₁)
    (x : pSpec₁.FullTranscript × Stmt₂ × Reduction.CutState P) (s₂ : Stmt₂)
    (c : pSpec₂.ChalsBelow n) :
    ((liftM ((P.dropLeft (Stmt₂ := Stmt₂)).runFixed c s₂
          (cast (Prover.prvState_cut_eq P) x.2.2)) :
          OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)
        >>= ksTailAfterProver verify E₁ E₂ V₂ P stmtIn x s₂)
      = (liftM (ksTailBase verify E₁ E₂ V₂ P stmtIn x s₂ c) :
          OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _) := by
  rw [ksTailBase, liftM_bind]
  refine bind_congr fun y => ?_
  rw [ksTailAfterProver, liftM_bind]
  refine bind_congr fun o₃ => ?_
  cases o₃ with
  | none => simp
  | some s₃ =>
    simp only [Option.elim, liftM_bind]
    refine bind_congr fun w₂? => ?_
    simp only [liftM_bind, liftM_pure]

/-- The appended game with the second half's challenges hardwired, as a computation of the *first*
protocol's spec: the first half's run, then the whole hardwired tail. -/
def ksGameTwo (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (c : pSpec₂.ChalsBelow n) (stmtOut : Stmt₂) (stmtIn : Stmt₁) (witIn : Wit₁) :
    OracleComp (oSpec + [pSpec₁.Challenge]ₒ)
      (Option ((Stmt₁ × Option Wit₁ × Stmt₃ × Wit₃) × Stmt₂ × Option Wit₂)) :=
  (P.takeLeft stmtOut).run stmtIn witIn >>= fun x =>
    (liftM (ksTailBase verify E₁ E₂ V₂ P stmtIn x (verify stmtIn x.1) c) :
      OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)

/-- The `ε₁` branch's event, weakened to what the first component's game measures: `E₂` produced a
witness, and `E₁` failed on it while it was good for `rel₂`. -/
def ksBadWeak (rel₁ : Set (Stmt₁ × Wit₁)) (rel₂ : Set (Stmt₂ × Wit₂)) :
    Option ((Stmt₁ × Option Wit₁ × Stmt₃ × Wit₃) × Stmt₂ × Option Wit₂) → Prop :=
  fun a => Option.elim a False fun p =>
    ∃ w₂, p.2.2 = some w₂ ∧ ksBad rel₁ rel₂ (p.1.1, p.1.2.1, p.2.1, w₂)

/-- The `ε₁` branch implies its weakening. -/
theorem ksBadWeak_of_branch (rel₁ : Set (Stmt₁ × Wit₁)) (rel₂ : Set (Stmt₂ × Wit₂))
    (rel₃ : Set (Stmt₃ × Wit₃))
    (a : Option ((Stmt₁ × Option Wit₁ × Stmt₃ × Wit₃) × Stmt₂ × Option Wit₂))
    (h : ((fun o => Option.elim o False (ksBad rel₁ rel₃)) ∘ Option.map Prod.fst) a
      ∧ Option.elim a False fun p => ∃ w₂ ∈ p.2.2, (p.2.1, w₂) ∈ rel₂) :
    ksBadWeak rel₁ rel₂ a := by
  obtain ⟨h₁, h₂⟩ := h
  cases a with
  | none => exact h₁
  | some p =>
    obtain ⟨w₂, hw₂, hmem⟩ := h₂
    exact ⟨w₂, hw₂, h₁.1, hmem⟩

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **The first component's game against the extracting adversary**, written out. Everything after
the first half's run is an `oSpec` computation: the second half with `c` hardwired, then `E₂`, then
`E₁` -- the last of these run by the *game*, not by the adversary, but `oSpec`-only either way. -/
def ksGameOne (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (c : pSpec₂.ChalsBelow n) (stmtOut : Stmt₂) (junk : Wit₂)
    (stmtIn : Stmt₁) (witIn : Wit₁) :
    OracleComp (oSpec + [pSpec₁.Challenge]ₒ)
      (Option (Stmt₁ × Option Wit₁ × Stmt₂ × Wit₂)) :=
  (P.takeLeft stmtOut).run stmtIn witIn >>= fun p =>
    (liftM (do
      let y ← (P.dropLeft (Stmt₂ := Stmt₂)).runFixed c stmtOut
                (cast (Prover.prvState_cut_eq P) p.2.2)
      let w₂? ← (E₂ (verify stmtIn p.1) y.2.2 y.1 [] []).run
      let w₁? ← (E₁ stmtIn (w₂?.getD junk) p.1 [] []).run
      pure (some (stmtIn, w₁?, verify stmtIn p.1, w₂?.getD junk))) :
        OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- The first component's game against `Prover.takeLeftExtract` is `ksGameOne`. -/
theorem ksExec_takeLeftExtract_run (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (hV₁ : V₁ = ⟨fun s t => pure (verify s t)⟩)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (c : pSpec₂.ChalsBelow n) (stmtOut : Stmt₂) (junk : Wit₂)
    (stmtIn : Stmt₁) (witIn : Wit₁) :
    (ksExec E₁ V₁ (P.takeLeftExtract verify E₂ c stmtOut junk) stmtIn witIn).run
      = ksGameOne verify E₁ E₂ P c stmtOut junk stmtIn witIn := by
  rw [ksExec_run_eq, Reduction.run_run_flat, Prover.takeLeftExtract_run, ksGameOne]
  subst hV₁
  simp only [OptionT.run_pure, liftM_pure, bind_assoc, pure_bind, Option.elim, liftM_bind]

omit [∀ i, SampleableType (pSpec₂.Challenge i)] in
open scoped NNReal in
/-- **The `ε₁` comparison.** The hardwired appended game is dominated by the first component's
game against `Prover.takeLeftExtract`: they run the same first half and the same hardwired second
half, and then the appended one additionally runs `V₂` -- which can only lose mass, and whose
output the weakened event does not read. -/
theorem probEvent_ksGameTwo_le (implP : QueryImpl oSpec ProbComp)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (c : pSpec₂.ChalsBelow n) (stmtOut : Stmt₂) (junk : Wit₂)
    (stmtIn : Stmt₁) (witIn : Wit₁) :
    Pr[ ksBadWeak rel₁ rel₂ | simulateQ (implP.addLift challengeQueryImpl :
        QueryImpl (oSpec + [pSpec₁.Challenge]ₒ) ProbComp)
        (ksGameTwo verify E₁ E₂ V₂ P c stmtOut stmtIn witIn)]
      ≤ Pr[ fun o => Option.elim o False (ksBad rel₁ rel₂) |
          simulateQ (implP.addLift challengeQueryImpl :
            QueryImpl (oSpec + [pSpec₁.Challenge]ₒ) ProbComp)
            (ksGameOne verify E₁ E₂ P c stmtOut junk stmtIn witIn)] := by
  classical
  rw [ksGameTwo, ksGameOne, simulateQ_bind]
  conv_rhs => rw [simulateQ_bind]
  rw [probEvent_bind_eq_tsum]
  conv_rhs => rw [probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl ?_
  rw [Prover.simulateQ_addLift_base, Prover.simulateQ_addLift_base, ksTailBase,
    simulateQ_bind]
  conv_rhs => rw [simulateQ_bind]
  rw [probEvent_bind_eq_tsum]
  conv_rhs => rw [probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun y => mul_le_mul' le_rfl ?_
  rw [simulateQ_bind]
  refine probEvent_bind_le_of_forall_le fun o₃ _ => ?_
  cases o₃ with
  | none => simp [ksBadWeak, simulateQ_pure, probEvent_pure]
  | some s₃ =>
    simp only [Option.elim, simulateQ_bind]
    rw [probEvent_bind_eq_tsum]
    conv_rhs => rw [probEvent_bind_eq_tsum]
    refine ENNReal.tsum_le_tsum fun w₂? => mul_le_mul' le_rfl ?_
    cases w₂? with
    | none => simp [ksBadWeak]
    | some w₂ =>
      simp only [Option.getD]
      rw [probEvent_bind_eq_tsum]
      conv_rhs => rw [probEvent_bind_eq_tsum]
      refine ENNReal.tsum_le_tsum fun w₁? => mul_le_mul' le_rfl ?_
      simp only [simulateQ_pure]
      rw [probEvent_pure, probEvent_pure]
      have himp : ksBadWeak rel₁ rel₂
            (some ((stmtIn, w₁?, s₃, y.2.2), verify stmtIn x.1, some w₂)) →
          Option.elim (some (stmtIn, w₁?, verify stmtIn x.1, w₂)) False
            (ksBad rel₁ rel₂) := by
        rintro ⟨w, hw, hb⟩
        cases hw
        exact hb
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact absurd (himp h1) h2
      · exact zero_le
      · exact le_rfl

omit [∀ i, SampleableType (pSpec₁.Challenge i)] in
open scoped NNReal in
/-- `evalDist_ksTailRight_drawFirst` under a stateless handler, with the state threaded. The
state is never read, so both sides are the `ProbComp` statement paired with the initial state. -/
theorem evalDist_ksTailRight_drawFirst_stateT (hst : impl.IsStateless)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (stmtIn : Stmt₁)
    (x : pSpec₁.FullTranscript × Stmt₂ × Reduction.CutState P) (s₂ : Stmt₂) (s₁ : σ) :
    𝒟[StateT.run (simulateQ (Reduction.pImplOf pSpec₂ impl)
        (ksTailRight verify E₁ E₂ V₂ P stmtIn x s₂)) s₁]
      = 𝒟[pSpec₂.drawChalsBelow n le_rfl >>= fun c =>
          StateT.run (simulateQ (Reduction.pImplOf pSpec₂ impl)
            ((liftM ((P.dropLeft (Stmt₂ := Stmt₂)).runFixed c s₂
                (cast (Prover.prvState_cut_eq P) x.2.2)) :
                OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)
              >>= ksTailAfterProver verify E₁ E₂ V₂ P stmtIn x s₂)) s₁] := by
  have hbase := QueryImpl.isStateless_addLift_apply hst (challengeQueryImpl (pSpec := pSpec₂))
  have hmapout : (pSpec₂.drawChalsBelow n le_rfl >>= fun c =>
        StateT.run (simulateQ (Reduction.pImplOf pSpec₂ impl)
          ((liftM ((P.dropLeft (Stmt₂ := Stmt₂)).runFixed c s₂
              (cast (Prover.prvState_cut_eq P) x.2.2)) :
              OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)
            >>= ksTailAfterProver verify E₁ E₂ V₂ P stmtIn x s₂)) s₁)
      = (fun a => (a, s₁)) <$> (pSpec₂.drawChalsBelow n le_rfl >>= fun c =>
          simulateQ (hst.base.addLift challengeQueryImpl :
              QueryImpl (oSpec + [pSpec₂.Challenge]ₒ) ProbComp)
            ((liftM ((P.dropLeft (Stmt₂ := Stmt₂)).runFixed c s₂
                (cast (Prover.prvState_cut_eq P) x.2.2)) :
                OracleComp (oSpec + [pSpec₂.Challenge]ₒ) _)
              >>= ksTailAfterProver verify E₁ E₂ V₂ P stmtIn x s₂)) :=
    Eq.trans (bind_congr fun c => QueryImpl.simulateQ_run_of_apply hbase _ s₁)
      (map_bind _ _ _).symm
  rw [QueryImpl.simulateQ_run_of_apply hbase, evalDist_map,
    evalDist_ksTailRight_drawFirst hst.base verify E₁ E₂ V₂ P stmtIn x s₂, hmapout, evalDist_map]

open OracleComp.DeferredSampling in
open scoped NNReal in
/-- **A stateless handler and a lossless `init` collapse a game to a plain `ProbComp`.** The
handler's state is never read, so the initial state drops out; `hinit` is what stops `init`'s own
failure mass from lowering the probability.

Both sides of the `ε₁` comparison are put in this form, because the reordering and eager-sampling
steps it needs are stated for `ProbComp`. -/
theorem probEvent_collapse {N : ℕ} {pSpec : ProtocolSpec N}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (hst : impl.IsStateless) (hinit : Pr[⊥ | init] = 0)
    {α : Type} (Y : OracleComp (oSpec + [pSpec.Challenge]ₒ) α) (p : α → Prop) :
    Pr[ p | init >>= fun s => StateT.run' (simulateQ
        (QueryImpl.addLift impl challengeQueryImpl :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) Y) s]
      = Pr[ p | simulateQ (hst.base.addLift challengeQueryImpl :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp) Y] := by
  refine probEvent_of_evalDist_eq ?_ p
  rw [show (fun s : σ => StateT.run' (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) Y) s)
      = fun _ : σ => simulateQ (hst.base.addLift challengeQueryImpl :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp) Y from
    funext fun s => QueryImpl.simulateQ_run'_of_apply
      (QueryImpl.isStateless_addLift_apply hst challengeQueryImpl) Y s]
  exact evalDist_bind_const_neverFails init hinit _

open scoped NNReal in
/-- **The `ε₂` half of the union bound.** On the runs where `E₂` produced no witness for `rel₂`,
the appended game is `V₂`'s knowledge-soundness game against the adversary's second half. -/
theorem probEvent_ksExecInstr_le_two [Nonempty Wit₂]
    (hcomm : (Reduction.pImplOf (pSpec₁ ++ₚ pSpec₂) impl).IsCommutative)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    {E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂} (hE₂ : E₂.IsLogIndependent)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (hV₁ : V₁ = ⟨fun s t => pure (verify s t)⟩)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (stmtOut : Stmt₂)
    (stmtIn : Stmt₁) (witIn : Wit₁) {ε₂ : ℝ≥0}
    (h₂ : ∀ s : σ, V₂.knowledgeSoundnessWith (pure s) impl rel₂ rel₃ E₂ ε₂) :
    Pr[ fun a => ((fun o => Option.elim o False (ksBad rel₁ rel₃)) ∘ Option.map Prod.fst) a
          ∧ ¬ Option.elim a False fun p => ∃ w₂ ∈ p.2.2, (p.2.1, w₂) ∈ rel₂
      | init >>= fun s => StateT.run' (simulateQ (Reduction.pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
          (ksExecInstr verify E₁ E₂ V₁ V₂ P stmtIn witIn).run) s] ≤ ε₂ := by
  classical
  have hmono : ∀ a : Option ((Stmt₁ × Option Wit₁ × Stmt₃ × Wit₃) × Stmt₂ × Option Wit₂),
      (((fun o => Option.elim o False (ksBad rel₁ rel₃)) ∘ Option.map Prod.fst) a
          ∧ ¬ Option.elim a False fun p => ∃ w₂ ∈ p.2.2, (p.2.1, w₂) ∈ rel₂) →
        Option.elim a False fun p =>
          ksBad rel₂ rel₃ (p.2.1, p.2.2, p.1.2.2.1, p.1.2.2.2) := by
    rintro (_ | p) ⟨h, h'⟩
    · exact h
    · exact ⟨fun w hw hmem => h' ⟨w, hw, hmem⟩, h.2⟩
  refine le_trans (probEvent_mono fun a _ ha => hmono a ha) ?_
  have hsplit : 𝒟[init >>= fun s => StateT.run (simulateQ
        (Reduction.pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
        (ksExecInstr verify E₁ E₂ V₁ V₂ P stmtIn witIn).run) s]
      = 𝒟[init >>= fun s => (StateT.run (simulateQ
            (Reduction.pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
            (Reduction.soundPhase₁ P V₁ stmtOut stmtIn witIn)) s >>= fun p =>
          StateT.run (simulateQ (Reduction.pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
            (ksTail verify E₁ E₂ V₂ P stmtOut stmtIn p.1)) p.2)] := by
    rw [evalDist_bind, evalDist_bind]
    exact congrArg _ (funext fun s =>
      evalDist_ksExecInstr_split hcomm verify E₁ E₂ V₁ V₂ P stmtOut stmtIn witIn s)
  simp only [Reduction.stateT_run'_eq, ← map_bind, probEvent_map]
  rw [probEvent_of_evalDist_eq hsplit]
  simp only [Reduction.soundPhase₁_det P V₁ stmtOut verify hV₁ stmtIn witIn, simulateQ_map,
    StateT.run_map, bind_map_left, ← bind_assoc]
  refine probEvent_bind_le_of_forall_le fun q _ => ?_
  rw [ksTail_eq verify E₁ E₂ V₂ P stmtOut stmtIn q.1 (verify stmtIn q.1.1) rfl,
    ← probEvent_map, ← Reduction.stateT_run'_eq,
    probEvent_of_evalDist_eq (Reduction.evalDist_stateT_run'_congr
      (Reduction.evalDist_simulateQ_liftM_right (impl := impl) (pSpec₁ := pSpec₁)
        (ksTailRight verify E₁ E₂ V₂ P stmtIn q.1 (verify stmtIn q.1.1)) q.2))]
  exact probEvent_ksTailRight_le hE₂ verify E₁ V₂ P stmtIn h₂ q.1 _ q.2

/-! The composition theorem itself is not here yet: what is above is the shape it needs -- the
game taken log-free, instrumented with the two values the union bound splits on, and split at the
cut. What remains is the two branch bounds, `ε₂` from `h₂` against the adversary's second half and
`ε₁` from `h₁` against `Prover.takeLeftExtract`, and their assembly by
`OracleComp.probEvent_le_add_split`. -/
end Verifier

end Compose
