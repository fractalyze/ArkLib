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


/-- The state at the cut, as `takeLeft` leaves it and as `dropLeft` takes it in. Definitional,
but `rw` works at `instances` transparency and neither `Fin.natAdd` nor `Fin.castLE` unfolds
there, so the transport has to be spelled out for the two halves to compose. -/
theorem takeLeft_prvState_cut :
    (P.takeLeft stmtOut).PrvState ⟨m, by omega⟩
      = P.PrvState (rightIdx m (0 : Fin (n + 1))) := rfl

/-- After the cut, the split-off prover's private state is the original's. Definitional:
`rightIdx` is `Fin.natAdd`, which only shifts the value by `m`. -/
theorem dropLeft_prvState (w : ℕ) (hw : w ≤ n) :
    P.PrvState ⟨m + w, by omega⟩ = (P.dropLeft (Stmt₂ := Stmt₂)).PrvState ⟨w, by omega⟩ := rfl

set_option maxHeartbeats 4000000 in
-- As in `takeLeft_processRound`: unfolding `dropLeft` drags its field-level casts through the
-- round's `dcast`s. Raised limit.
/-- One round after the cut: the original prover's round is the tail prover's, lifted. The
`pSpec₁` half of the transcript is already fixed, so it rides along as `T₁`. -/
theorem dropLeft_processRound (w : ℕ) (hw : w < n) (hmw : m + w < m + n)
    (T₁ : pSpec₁.FullTranscript)
    (X : OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
          (pSpec₂.Transcript ⟨w, by omega⟩ ×
            (P.dropLeft (Stmt₂ := Stmt₂)).PrvState ⟨w, by omega⟩)) :
    Prover.processRound ⟨m + w, hmw⟩ P
        ((fun p => (liftTranscriptR (pSpec₁ := pSpec₁) w (by omega) T₁ p.1,
                    cast (dropLeft_prvState (Stmt₂ := Stmt₂) P w (by omega)).symm p.2))
          <$> liftM X)
      = (fun p => (liftTranscriptR (pSpec₁ := pSpec₁) (w + 1) (by omega) T₁ p.1,
                   cast (dropLeft_prvState (Stmt₂ := Stmt₂) P (w + 1) (by omega)).symm p.2))
        <$> liftM (Prover.processRound ⟨w, hw⟩ (P.dropLeft (Stmt₂ := Stmt₂)) X) := by
  unfold Prover.processRound
  simp only [map_bind, liftM_bind, bind_map_left]
  refine bind_congr fun p => ?_
  have hdir : (pSpec₁ ++ₚ pSpec₂).dir ⟨m + w, hmw⟩ = pSpec₂.dir ⟨w, hw⟩ :=
    dir_append_add (pSpec₁ := pSpec₁) w hw hmw
  split
  · rename_i hDirA
    split
    · rename_i hDirB
      simp only [Prover.dropLeft, liftM_map, liftM_bind, map_bind, liftM_liftM_base_right,
        liftM_liftM_getChallenge_inr, bind_map_left, bind_pure_comp, cast_cast, cast_eq,
        Functor.map_map, ChallengeIdx.inr, Fin.natAdd]
      refine bind_congr fun a => ?_
      congr 1
      funext ch
      rw [liftTranscriptR_concat (pSpec₁ := pSpec₁) w hw T₁]
      congr 2
      exact (eq_of_heq ((cast_heq _ _).trans (cast_heq _ ch))).symm
    · rename_i hDirB
      exact Direction.noConfusion ((hdir.symm.trans hDirA).symm.trans hDirB)
  · rename_i hDirA
    split
    · rename_i hDirB
      exact Direction.noConfusion ((hdir.symm.trans hDirA).symm.trans hDirB)
    · rename_i hDirB
      simp only [Prover.dropLeft, bind_pure_comp, liftM_map, liftM_liftM_base_right, cast_cast,
        cast_eq, Functor.map_map, MessageIdx.inr, Fin.natAdd]
      congr 1
      funext x
      congr 1
      rw [liftTranscriptR_concat (pSpec₁ := pSpec₁) w hw T₁]
      simp only [cast_cast, cast_eq]

set_option maxHeartbeats 4000000 in
-- Each induction step re-elaborates `dropLeft_processRound`'s statement, casts included.
-- Raised limit.
/-- **The round induction after the cut.** Past the cut the original prover's partial run is
`takeLeft`'s full run followed by `dropLeft`'s partial run, with the two transcripts combined by
`liftTranscriptR`.

Unlike `AppendProver`'s `append_runToRound_ge` this holds from `w = 0`: there is no boundary
round to special-case, because `dropLeft` hands the state across unchanged (`input` is the second
projection) rather than through an `output`/`input` pair. -/
theorem dropLeft_runToRound (stmt : Stmt₁) (wit : Wit₁) :
    ∀ (w : ℕ) (hw : w ≤ n),
    P.runToRound ⟨m + w, by omega⟩ stmt wit
      = (do
          let p ← liftM ((P.takeLeft stmtOut).runToRound ⟨m, by omega⟩ stmt wit)
          let q ← liftM ((P.dropLeft (Stmt₂ := Stmt₂)).runToRound ⟨w, by omega⟩ stmtOut
                    (cast (takeLeft_prvState_cut P stmtOut) p.2))
          return (liftTranscriptR (pSpec₁ := pSpec₁) w hw p.1 q.1,
                  cast (dropLeft_prvState (Stmt₂ := Stmt₂) P w hw).symm q.2)) := by
  intro w
  induction w with
  | zero =>
    intro hw
    change P.runToRound ⟨m, by omega⟩ stmt wit = _
    rw [takeLeft_runToRound P stmtOut stmt wit m le_rfl (by omega)]
    simp only [runToRound_mk_zero, liftTranscriptR_zero, Prover.dropLeft]
    rw [← bind_pure_comp]
    exact bind_congr fun p => rfl
  | succ w ih =>
    intro hw
    refine Eq.trans (Prover.runToRound_mk_succ P (m + w) (by omega) stmt wit) ?_
    rw [ih (by omega)]
    refine Eq.trans (processRound_bind ⟨m + w, by omega⟩ P _ _) ?_
    refine bind_congr fun p => ?_
    rw [Prover.runToRound_mk_succ (P.dropLeft (Stmt₂ := Stmt₂)) w (by omega)]
    simp only [bind_pure_comp]
    exact dropLeft_processRound P w (by omega) (by omega) p.1 _


/-- `takeLeft`'s output witness type is `dropLeft`'s input witness type: both are the original
prover's state at the cut. Spelled out for the same `instances`-transparency reason as
`takeLeft_prvState_cut`. -/
theorem prvState_cut_eq :
    P.PrvState (leftIdx n (Fin.last m)) = P.PrvState (rightIdx m (0 : Fin (n + 1))) := rfl

/-- **The prover splits.** Running an appended prover is running its first `m` rounds, handing the
private state across the cut, and running the remaining `n` -- with the transcripts concatenated
and the output the original's, produced by `dropLeft.output`.

This is the converse of `Prover.append_run`, and the form the soundness composition theorems need:
there the prover is an arbitrary adversary for `pSpec₁ ++ₚ pSpec₂`, not one built by
`Prover.append`. `stmtOut` is the statement `takeLeft` reports and `dropLeft` is fed; it is
arbitrary because nothing downstream reads it -- the soundness event reads the *verifier*'s
output. -/
theorem run_eq_takeLeft_dropLeft (stmt : Stmt₁) (wit : Wit₁) :
    P.run stmt wit = (do
      let p ← liftM ((P.takeLeft stmtOut).run stmt wit)
      let q ← liftM ((P.dropLeft (Stmt₂ := Stmt₂)).run stmtOut (cast (prvState_cut_eq P) p.2.2))
      return (p.1 ++ₜ q.1, q.2.1, q.2.2)) := by
  unfold Prover.run
  rw [runToRound_last, dropLeft_runToRound P stmtOut stmt wit n le_rfl]
  simp only [runToRound_last, Prover.takeLeft, Prover.dropLeft, liftM_bind, liftM_map, map_bind,
    bind_assoc, bind_map_left, liftM_pure, pure_bind, liftTranscriptR_full,
    liftM_liftM_base_right, bind_pure_comp, Functor.map_map]
  refine Eq.trans (bind_assoc _ _ _) (bind_congr fun p => ?_)
  refine Eq.trans (map_bind_left _ _ _) (bind_congr fun a => ?_)
  rfl

end Prover
