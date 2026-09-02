/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendCompleteness

/-!
# Splitting a prover for an appended protocol

`Prover.append` builds a prover for `pSpec₁ ++ₚ pSpec₂` out of two component provers. The
soundness composition theorems need the *converse*: an adversarial prover for the appended
protocol is arbitrary, not of that form, and the hypotheses `h₁` and `h₂` speak about provers
for `pSpec₁` and `pSpec₂` separately.

`Prover.takeLeft` keeps the first `m` rounds and hands its final private state out as the
output witness -- the witness type in the soundness game is universally quantified, so it can
carry whatever the second half needs. `Prover.dropLeft` takes that state back in as its input
witness and runs the remaining `n` rounds.

The index bookkeeping is `Fin.castLE` on the left and `Fin.natAdd` on the right, with the
round types transported by `ProtocolSpec.append_Type_castAdd` / `_natAdd`.
-/

open OracleComp OracleSpec ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

namespace Prover

/-- The index in the appended protocol of the left component's round `i`. -/
@[reducible] def leftIdx (n : ℕ) (i : Fin (m + 1)) : Fin (m + n + 1) := Fin.castLE (by omega) i

/-- The index in the appended protocol of the right component's round `j`. -/
@[reducible] def rightIdx (m : ℕ) (j : Fin (n + 1)) : Fin (m + n + 1) := Fin.natAdd m j

/-- **The first `m` rounds of an appended prover.** The output statement is supplied (it plays
no role -- the soundness event reads the *verifier's* output), and the output witness is the
prover's own private state at the cut, which `dropLeft` takes back in. -/
def takeLeft (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (stmtOut : Stmt₂) :
    Prover oSpec Stmt₁ Wit₁ Stmt₂ (P.PrvState (leftIdx n (Fin.last m))) pSpec₁ where
  PrvState := fun i => P.PrvState (leftIdx n i)
  input := fun ctx => cast (congrArg P.PrvState (by ext; simp [leftIdx])) (P.input ctx)
  sendMessage := fun i state => do
    let r ← P.sendMessage (MessageIdx.inl i)
      (cast (congrArg P.PrvState (by ext; simp [leftIdx, MessageIdx.inl])) state)
    return (cast (message_append_inl (pSpec₂ := pSpec₂) i) r.1,
      cast (congrArg P.PrvState (by ext; simp [leftIdx, MessageIdx.inl])) r.2)
  receiveChallenge := fun i state => do
    let f ← P.receiveChallenge (ChallengeIdx.inl i)
      (cast (congrArg P.PrvState (by ext; simp [leftIdx, ChallengeIdx.inl])) state)
    return fun c => cast (congrArg P.PrvState (by ext; simp [leftIdx, ChallengeIdx.inl]))
      (f (cast (challenge_append_inl (pSpec₂ := pSpec₂) i).symm c))
  output := fun state => pure (stmtOut, state)

/-- **The last `n` rounds of an appended prover**, started from a private state at the cut --
which arrives as the input witness. -/
def dropLeft (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) :
    Prover oSpec Stmt₂ (P.PrvState (rightIdx m (0 : Fin (n + 1)))) Stmt₃ Wit₃ pSpec₂ where
  PrvState := fun j => P.PrvState (rightIdx m j)
  input := fun ctx => ctx.2
  sendMessage := fun j state => do
    let r ← P.sendMessage (MessageIdx.inr j)
      (cast (congrArg P.PrvState (by ext; simp [rightIdx, MessageIdx.inr])) state)
    return (cast (message_append_inr (pSpec₁ := pSpec₁) j) r.1,
      cast (congrArg P.PrvState (by ext; simp [rightIdx, MessageIdx.inr] ; omega)) r.2)
  receiveChallenge := fun j state => do
    let f ← P.receiveChallenge (ChallengeIdx.inr j)
      (cast (congrArg P.PrvState (by ext; simp [rightIdx, ChallengeIdx.inr])) state)
    return fun c => cast (congrArg P.PrvState (by ext; simp [rightIdx, ChallengeIdx.inr] ; omega))
      (f (cast (challenge_append_inr (pSpec₁ := pSpec₁) j).symm c))
  output := fun state =>
    P.output (cast (congrArg P.PrvState (by ext; simp [rightIdx])) state)

end Prover
