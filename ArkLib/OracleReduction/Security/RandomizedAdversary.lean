/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Security.Basic
import ArkLib.ToVCVio.EvalDist.CompletenessBound

/-!
# Randomized adversaries

A `Prover oSpec …` gets its randomness from `oSpec`, so at `oSpec = []ₒ` -- the instantiation every
concrete protocol in this library uses -- a single prover term is *deterministic*. The security
definitions in `Security/Basic.lean` quantify over provers, so it is worth recording why that
costs nothing.

It costs nothing because the definitions demand the bound for **every** prover, and a randomized
adversary's success probability is an average of deterministic ones. Modelling a randomized
adversary as a family `P : ρ → Prover …` with its parameter drawn from `aux : ProbComp ρ`, the
bound transfers by `probEvent_bind_le_of_forall_le` -- that is all the lemmas below are.

The converse -- that every prover over a larger, randomness-carrying spec *is* such a family --
holds by fixing the random tape in advance, but needs a bound on the number of samples a prover
makes and is not needed by anything here.

The consumer is sequential composition of knowledge soundness. There the first component's
adversary has to output an intermediate witness that only exists once the *second* half has run,
which needs the second half's challenges; hardwiring them and averaging with
`knowledgeSoundnessWith_randomized` is what makes that adversary a legal `Prover oSpec …`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {StmtIn StmtOut : Type}
  {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {V : Verifier oSpec StmtIn StmtOut pSpec}

open scoped NNReal in
/-- **Soundness holds against a randomized adversary.** The adversary is a family of provers
indexed by a parameter drawn from `aux`; each member is covered by `soundness`, and the bound
survives the average. -/
theorem soundness_randomized {langIn : Set StmtIn} {langOut : Set StmtOut} {ε : ℝ≥0}
    (h : V.soundness init impl langIn langOut ε)
    {WitIn WitOut ρ : Type} (aux : ProbComp ρ)
    (witIn : ρ → WitIn) (P : ρ → Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (hstmtIn : stmtIn ∉ langIn) :
    Pr[ fun r : (pSpec.FullTranscript × StmtOut × WitOut) × StmtOut => r.2 ∈ langOut |
        OptionT.mk (aux >>= fun r => init >>= fun s =>
          StateT.run' (simulateQ (QueryImpl.addLift impl challengeQueryImpl)
            (Reduction.run stmtIn (witIn r) (Reduction.mk (P r) V)).run) s)] ≤ ε := by
  rw [OptionT.probEvent_mk]
  refine probEvent_bind_le_of_forall_le fun r _ => ?_
  have hc := h WitIn WitOut (witIn r) (P r) stmtIn hstmtIn
  dsimp only at hc
  rw [OptionT.probEvent_mk] at hc
  exact hc

variable {WitIn WitOut : Type}

open scoped NNReal in
/-- **Knowledge soundness holds against a randomized adversary**, for the extractor already
certified. Stated for `knowledgeSoundnessWith` rather than `knowledgeSoundness` because the
extractor is chosen before the adversary, so one `E` serves the whole family -- which is exactly
what the averaging needs. -/
theorem knowledgeSoundnessWith_randomized {relIn : Set (StmtIn × WitIn)}
    {relOut : Set (StmtOut × WitOut)}
    {E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec} {ε : ℝ≥0}
    (h : V.knowledgeSoundnessWith init impl relIn relOut E ε)
    {ρ : Type} (aux : ProbComp ρ) (witIn : ρ → WitIn)
    (P : ρ → Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmtIn : StmtIn) :
    Pr[ fun p : StmtIn × Option WitIn × StmtOut × WitOut =>
          (∀ w ∈ p.2.1, (p.1, w) ∉ relIn) ∧ (p.2.2.1, p.2.2.2) ∈ relOut |
        OptionT.mk (aux >>= fun r => init >>= fun s =>
          StateT.run' (simulateQ (QueryImpl.addLift impl challengeQueryImpl)
            (do
              let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
                ← (Reduction.mk (P r) V).runWithLog stmtIn (witIn r)
              let extractedWitIn? ←
                liftM (E stmtIn witOut transcript proveQueryLog.fst verifyQueryLog).run
              return (stmtIn, extractedWitIn?, stmtOut, witOut) :
                OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) _).run) s)] ≤ ε := by
  rw [OptionT.probEvent_mk]
  refine probEvent_bind_le_of_forall_le fun r _ => ?_
  have hc := h stmtIn (witIn r) (P r)
  dsimp only at hc
  rw [OptionT.probEvent_mk] at hc
  exact hc

end Verifier
