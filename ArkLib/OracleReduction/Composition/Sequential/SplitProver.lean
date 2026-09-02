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
      cast (congrArg P.PrvState (by ext; simp [rightIdx, MessageIdx.inr]; omega)) r.2)
  receiveChallenge := fun j state => do
    let f ← P.receiveChallenge (ChallengeIdx.inr j)
      (cast (congrArg P.PrvState (by ext; simp [rightIdx, ChallengeIdx.inr])) state)
    return fun c => cast (congrArg P.PrvState (by ext; simp [rightIdx, ChallengeIdx.inr]; omega))
      (f (cast (challenge_append_inr (pSpec₁ := pSpec₁) j).symm c))
  output := fun state =>
    P.output (cast (congrArg P.PrvState (by ext; simp [rightIdx])) state)


variable (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) (stmtOut : Stmt₂)

/-- Before the cut, the split-off prover's private state is the original's. Definitional:
`leftIdx` is `Fin.castLE`, which only rewrites the bound. -/
theorem takeLeft_prvState (v : ℕ) (hv : v ≤ m) :
    P.PrvState ⟨v, by omega⟩ = (P.takeLeft stmtOut).PrvState ⟨v, by omega⟩ := rfl

set_option maxHeartbeats 4000000 in
-- Unfolding `takeLeft` drags its field-level casts through the round's `dcast`s, so the defeq
-- checks closing each branch are large. Raised limit.
/-- One round before the cut: the original prover's round is the split-off prover's, lifted. -/
theorem takeLeft_processRound (v : ℕ) (hv : v < m) (hvn : v < m + n)
    (X : OracleComp (oSpec + [pSpec₁.Challenge]ₒ)
          (pSpec₁.Transcript ⟨v, by omega⟩ × (P.takeLeft stmtOut).PrvState ⟨v, by omega⟩)) :
    Prover.processRound ⟨v, hvn⟩ P
        ((fun p => (liftTranscript (pSpec₂ := pSpec₂) v (by omega) (by omega) p.1,
                    cast (takeLeft_prvState P stmtOut v (by omega)).symm p.2)) <$> liftM X)
      = (fun p => (liftTranscript (pSpec₂ := pSpec₂) (v + 1) (by omega) (by omega) p.1,
                   cast (takeLeft_prvState P stmtOut (v + 1) (by omega)).symm p.2))
        <$> liftM (Prover.processRound ⟨v, hv⟩ (P.takeLeft stmtOut) X) := by
  unfold Prover.processRound
  simp only [map_bind, liftM_bind, bind_map_left]
  refine bind_congr fun p => ?_
  have hdir : (pSpec₁ ++ₚ pSpec₂).dir ⟨v, hvn⟩ = pSpec₁.dir ⟨v, hv⟩ :=
    dir_append_lt (pSpec₂ := pSpec₂) v hv hvn
  split
  · rename_i hDirA
    split
    · rename_i hDirB
      simp only [Prover.takeLeft, liftM_map, liftM_bind, map_bind, liftM_liftM_base,
        liftM_liftM_getChallenge_inl, bind_map_left, bind_pure_comp, cast_cast, cast_eq,
        Functor.map_map, ChallengeIdx.inl, Fin.castAdd, Fin.castLE]
      refine bind_congr fun a => ?_
      congr 1
      funext ch
      rw [liftTranscript_concat (pSpec₂ := pSpec₂) v hv hvn]
      congr 2
      exact (eq_of_heq ((cast_heq _ _).trans (cast_heq _ ch))).symm
    · rename_i hDirB
      exact Direction.noConfusion ((hdir.symm.trans hDirA).symm.trans hDirB)
  · rename_i hDirA
    split
    · rename_i hDirB
      exact Direction.noConfusion ((hdir.symm.trans hDirA).symm.trans hDirB)
    · rename_i hDirB
      simp only [Prover.takeLeft, bind_pure_comp, liftM_map, liftM_liftM_base, cast_cast,
        cast_eq, Functor.map_map, MessageIdx.inl, Fin.castAdd, Fin.castLE]
      congr 1
      funext x
      congr 1
      rw [liftTranscript_concat (pSpec₂ := pSpec₂) v hv hvn]
      simp only [cast_cast, cast_eq]


set_option maxHeartbeats 4000000 in
-- Each induction step re-elaborates `takeLeft_processRound`'s statement, casts included.
-- Raised limit.
/-- **The round induction before the cut.** The original prover's partial run, up to any round
at or before the cut, is the split-off prover's partial run, lifted into the appended protocol's
challenge oracle and with the transcript re-indexed. -/
theorem takeLeft_runToRound (stmt : Stmt₁) (wit : Wit₁) :
    ∀ (v : ℕ) (hv : v ≤ m) (hvn : v ≤ m + n),
    P.runToRound ⟨v, by omega⟩ stmt wit
      = (fun p => (liftTranscript (pSpec₂ := pSpec₂) v hv hvn p.1,
                   cast (takeLeft_prvState P stmtOut v hv).symm p.2))
        <$> liftM ((P.takeLeft stmtOut).runToRound ⟨v, by omega⟩ stmt wit) := by
  intro v
  induction v with
  | zero =>
    intro hv hvn
    rw [runToRound_mk_zero, runToRound_mk_zero]
    simp only [ChallengeIdx, Challenge]
    congr 1
    refine Prod.ext ?_ ?_
    · exact Subsingleton.elim _ _
    · simp [Prover.takeLeft]
  | succ v ih =>
    intro hv hvn
    rw [Prover.runToRound_mk_succ P v (by omega),
        Prover.runToRound_mk_succ (P.takeLeft stmtOut) v (by omega),
        ih (by omega) (by omega)]
    exact takeLeft_processRound P stmtOut v (by omega) (by omega) _

end Prover
