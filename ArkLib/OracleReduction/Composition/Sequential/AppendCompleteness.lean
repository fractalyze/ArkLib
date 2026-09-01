/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Composition.Sequential.HandlerCommutativity
import ArkLib.ToVCVio.EvalDist.CompletenessBound

open OracleComp OracleSpec ProtocolSpec

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
          let stmtOut ← (liftM (do
            let s₂ ← R₁.verifier.verify stmt x.1
            R₂.verifier.verify s₂ y.1).run : OptionT (Comp oSpec pSpec₁ pSpec₂) _)
          let s₃ ← stmtOut.getM
          pure ((x.1 ++ₜ y.1, y.2.1, y.2.2), s₃)) := by
  unfold Reduction.run Reduction.append
  dsimp only
  rw [Prover.append_run]
  simp only [Verifier.append, Verifier.run, liftM_bind, liftM_pure, bind_assoc, pure_bind,
    FullTranscript.append_fst, FullTranscript.append_snd]

end Reduction
