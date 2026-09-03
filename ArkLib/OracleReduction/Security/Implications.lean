/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.Salt
import ArkLib.OracleReduction.Security.SpecialSoundness
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness

/-!
# Implications between security notions

This file collects the implications between the various security notions.

For now, we only state the theorems. It's likely that we will split this file into multiple files in
a single `Implication` folder in the future, each file for the proof of a single implication.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Verifier

section Implications

/- TODO: add the following results
- `knowledgeSoundness` implies `soundness`
- `rbrSoundness` implies `soundness`
- `rbrKnowledgeSoundness` implies `rbrSoundness`
- `rbrKnowledgeSoundness` implies `knowledgeSoundness`

In other words, we have a lattice of security notions, with `knowledge` and `roundByRound` being
two strengthenings of soundness.
-/

/-- Knowledge soundness with knowledge error `knowledgeError < 1` implies soundness with the same
soundness error `knowledgeError`, and for the corresponding input and output languages. -/
theorem knowledgeSoundness_implies_soundness
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (knowledgeError : ℝ≥0) (hLt : knowledgeError < 1) :
      knowledgeSoundness init impl relIn relOut verifier knowledgeError →
        soundness init impl relIn.language relOut.language verifier knowledgeError := by
  simp [knowledgeSoundness, soundness, Set.language]
  intro extractor hKS WitIn' WitOut' witIn' prover stmtIn hStmtIn
  sorry
  -- have hKS' := hKS stmtIn witIn' prover
  -- clear hKS
  -- contrapose! hKS'
  -- constructor
  -- · convert hKS'; rename_i result
  --   obtain ⟨transcript, queryLog, stmtOut, witOut⟩ := result
  --   simp
  --   sorry
  -- · simp only [Set.language, Set.mem_setOf_eq, not_exists] at hStmtIn
  --   simp only [Functor.map, Seq.seq, PMF.bind_bind, Function.comp_apply, PMF.pure_bind, hStmtIn,
  --     PMF.bind_const, PMF.pure_apply, eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte,
  --     zero_add, ℝ≥0.coe_lt_one_iff, hLt]

/-- The challenge rounds strictly before round `m`. -/
def challengesBefore (m : Fin (n + 1)) : Finset pSpec.ChallengeIdx :=
  {i : pSpec.ChallengeIdx | (i.1 : ℕ) < (m : ℕ)}

omit [∀ i, SampleableType (pSpec.Challenge i)] in
theorem mem_challengesBefore {m : Fin (n + 1)} {i : pSpec.ChallengeIdx} :
    i ∈ challengesBefore (pSpec := pSpec) m ↔ (i.1 : ℕ) < (m : ℕ) := by
  simp [challengesBefore]

omit [∀ i, SampleableType (pSpec.Challenge i)] in
@[simp] theorem challengesBefore_zero :
    challengesBefore (pSpec := pSpec) 0 = ∅ := by
  simp [challengesBefore]

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- A prover-to-verifier round contributes no challenge index. -/
theorem challengesBefore_succ_of_dir_eq_P_to_V {m : Fin n} (hDir : pSpec.dir m = .P_to_V) :
    challengesBefore (pSpec := pSpec) m.succ = challengesBefore (pSpec := pSpec) m.castSucc := by
  ext i
  simp only [mem_challengesBefore, Fin.val_succ, Fin.val_castSucc]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact h
    · have hi : i.1 = m := Fin.ext h
      exact absurd (hi ▸ i.2) (by rw [hDir]; decide)
  · exact fun h => Nat.lt_succ_of_lt h

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- A verifier-to-prover round contributes exactly its own challenge index. -/
theorem challengesBefore_succ_of_dir_eq_V_to_P {m : Fin n} (hDir : pSpec.dir m = .V_to_P) :
    challengesBefore (pSpec := pSpec) m.succ
      = insert ⟨m, hDir⟩ (challengesBefore (pSpec := pSpec) m.castSucc) := by
  ext i
  simp only [Finset.mem_insert, mem_challengesBefore, Fin.val_succ, Fin.val_castSucc]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact Or.inr h
    · exact Or.inl (Subtype.ext (Fin.ext h))
  · rintro (rfl | h)
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt h

omit [∀ i, SampleableType (pSpec.Challenge i)] in
@[simp] theorem challengesBefore_last :
    challengesBefore (pSpec := pSpec) (Fin.last n) = Finset.univ := by
  ext i
  simp [mem_challengesBefore, i.1.isLt]

omit [∀ i, SampleableType (pSpec.Challenge i)] in
theorem notMem_challengesBefore_castSucc {m : Fin n} (hDir : pSpec.dir m = .V_to_P) :
    (⟨m, hDir⟩ : pSpec.ChallengeIdx) ∉ challengesBefore (pSpec := pSpec) m.castSucc := by
  simp [mem_challengesBefore]

/-- `ProtocolSpec.simulateQ_addLift_challengeQueryImpl_getChallenge` in the `liftM` spelling that
`Prover.processRound` actually produces: the coercion of `getChallenge` into the combined spec
elaborates through `MonadLift`, not through a literal `liftComp`. -/
theorem simulateQ_addLift_challengeQueryImpl_liftM_getChallenge (i : pSpec.ChallengeIdx) :
    simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (liftM (pSpec.getChallenge i) : OracleComp (oSpec + [pSpec.Challenge]ₒ) _)
      = (liftM ($ᵗ (pSpec.Challenge i)) : StateT σ ProbComp (pSpec.Challenge i)) :=
  ProtocolSpec.simulateQ_addLift_challengeQueryImpl_getChallenge impl i

/-- Along the prover's run, a state function that starts false can only turn true at a challenge
round, so its probability after round `m` is at most the sum of the round-by-round errors of the
challenge rounds before `m`.

The hypothesis is the worst-case-per-prefix bad-transition bound of `rbrSoundnessWorstCase`,
evaluated at the fixed input statement: for every challenge index and every transcript prefix, a
fresh uniform challenge flips the state function with probability at most the round's error. That
per-prefix shape is what a union bound over rounds needs — the averaged shape of `rbrSoundness`
bounds a mixture and does not by itself bound each prefix.

The initial oracle state `s` is a parameter rather than a sample from `init`: the induction has to
hand the state reached after round `m` to round `m + 1`, which a computation whose state has
already been discarded cannot do.

`toFun_empty` starts the state function false, `toFun_next` forbids a flip across a prover message,
and a flip across a challenge is exactly the bounded bad event. -/
theorem probEvent_stateFunction_runToRound_le
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    (stF : verifier.StateFunction init impl langIn langOut)
    {WitIn' WitOut' : Type} (witIn : WitIn')
    (prover : Prover oSpec StmtIn WitIn' StmtOut WitOut' pSpec)
    (stmtIn : StmtIn) (hStmtIn : stmtIn ∉ langIn)
    (hRbr : ∀ (i : pSpec.ChallengeIdx) (tr : pSpec.Transcript i.1.castSucc),
      Pr[ fun c => ¬ stF.toFun i.1.castSucc stmtIn tr ∧
            stF.toFun i.1.succ stmtIn (tr.concat c)
        | ($ᵗ (pSpec.Challenge i))] ≤ (rbrSoundnessError i : ENNReal))
    (m : Fin (n + 1)) (s : σ) :
    Pr[ fun x => stF.toFun m stmtIn x.1.1
      | (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (prover.runToRound m stmtIn witIn)).run s]
      ≤ ((∑ i ∈ challengesBefore (pSpec := pSpec) m, rbrSoundnessError i : ℝ≥0) : ENNReal) := by
  induction m using Fin.induction with
  | zero =>
    have hEmpty : ¬ stF.toFun 0 stmtIn default := fun h =>
      hStmtIn ((stF.toFun_empty stmtIn).mpr h)
    rw [challengesBefore_zero, show prover.runToRound 0 stmtIn witIn
      = pure ⟨default, prover.input (stmtIn, witIn)⟩ from rfl]
    simp only [Finset.sum_empty, ENNReal.coe_zero, nonpos_iff_eq_zero]
    refine probEvent_eq_zero fun x hx hp => ?_
    obtain rfl : x = ((default, prover.input (stmtIn, witIn)), s) := by simpa using hx
    exact hEmpty hp
  | succ m ih =>
    rw [Prover.runToRound_succ]
    cases hDir : pSpec.dir m with
    | P_to_V =>
      rw [Prover.processRound_of_dir_eq_P_to_V m hDir,
        challengesBefore_succ_of_dir_eq_P_to_V hDir, simulateQ_bind, StateT.run_bind]
      refine le_trans (probEvent_bind_le_probEvent
        (p := fun x => stF.toFun m.castSucc stmtIn x.1.1) ?_) ih
      rintro ⟨⟨tr, st⟩, s'⟩ - hp
      simp only [bind_pure_comp, simulateQ_map, StateT.run_map, probEvent_map]
      refine probEvent_eq_zero fun z _ hq => ?_
      exact stF.toFun_next m hDir stmtIn tr hp z.1.1 hq
    | V_to_P =>
      rw [Prover.processRound_of_dir_eq_V_to_P m hDir,
        challengesBefore_succ_of_dir_eq_V_to_P hDir,
        Finset.sum_insert (notMem_challengesBefore_castSucc hDir), simulateQ_bind,
        StateT.run_bind]
      refine le_trans (probEvent_bind_le_probEvent_add
        (p := fun x => stF.toFun m.castSucc stmtIn x.1.1)
        (ε := (rbrSoundnessError ⟨m, hDir⟩ : ENNReal)) ?_) ?_
      · rintro ⟨⟨tr, st⟩, s'⟩ - hp
        -- The prover's own queries for this round run *before* the challenge is drawn (see
        -- `Prover.processRound`), so peel them off first. They do not touch the transcript, and
        -- the round bound below is uniform in their outcome, so nothing is lost.
        rw [simulateQ_bind, StateT.run_bind]
        refine probEvent_bind_le_of_forall_le ?_
        rintro ⟨update, s''⟩ -
        rw [simulateQ_bind, simulateQ_addLift_challengeQueryImpl_liftM_getChallenge,
          StateT.run_bind]
        simp only [StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
        refine le_trans (probEvent_bind_le_probEvent
          (p := fun c => ¬ stF.toFun m.castSucc stmtIn tr ∧
            stF.toFun m.succ stmtIn (tr.concat c)) ?_) (hRbr ⟨m, hDir⟩ tr)
        intro c _ hpc
        simp only [simulateQ_pure, StateT.run_pure]
        refine probEvent_eq_zero fun z hz hq => ?_
        obtain rfl : z = ((Transcript.concat c tr, update c), s'') := by simpa using hz
        exact hpc ⟨hp, hq⟩
      · rw [ENNReal.coe_add, add_comm ((rbrSoundnessError ⟨m, hDir⟩ : ℝ≥0) : ENNReal)]
        exact add_le_add ih le_rfl

/-- The full-run specialization of `probEvent_stateFunction_runToRound_le`: after the last round,
the state function holds with probability at most the total round-by-round error. This is the
half of `rbrSoundness_implies_soundness` that the round structure alone gives; turning it into a
soundness bound additionally needs `StateFunction.toFun_full`, which samples the verifier's oracle
state afresh from `init` instead of inheriting the state the prover left behind. -/
theorem probEvent_stateFunction_run_le
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    (stF : verifier.StateFunction init impl langIn langOut)
    {WitIn' WitOut' : Type} (witIn : WitIn')
    (prover : Prover oSpec StmtIn WitIn' StmtOut WitOut' pSpec)
    (stmtIn : StmtIn) (hStmtIn : stmtIn ∉ langIn)
    (hRbr : ∀ (i : pSpec.ChallengeIdx) (tr : pSpec.Transcript i.1.castSucc),
      Pr[ fun c => ¬ stF.toFun i.1.castSucc stmtIn tr ∧
            stF.toFun i.1.succ stmtIn (tr.concat c)
        | ($ᵗ (pSpec.Challenge i))] ≤ (rbrSoundnessError i : ENNReal))
    (s : σ) :
    Pr[ fun x => stF.toFun (Fin.last n) stmtIn x.1.1
      | (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (prover.runToRound (Fin.last n) stmtIn witIn)).run s]
      ≤ ((∑ i, rbrSoundnessError i : ℝ≥0) : ENNReal) := by
  have := probEvent_stateFunction_runToRound_le init impl stF witIn prover stmtIn hStmtIn hRbr
    (Fin.last n) s
  rwa [challengesBefore_last] at this

/-- `probEvent_stateFunction_run_le` averaged over the initial oracle state, the shape the
soundness game presents. -/
theorem probEvent_stateFunction_run_le_of_init
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    (stF : verifier.StateFunction init impl langIn langOut)
    {WitIn' WitOut' : Type} (witIn : WitIn')
    (prover : Prover oSpec StmtIn WitIn' StmtOut WitOut' pSpec)
    (stmtIn : StmtIn) (hStmtIn : stmtIn ∉ langIn)
    (hRbr : ∀ (i : pSpec.ChallengeIdx) (tr : pSpec.Transcript i.1.castSucc),
      Pr[ fun c => ¬ stF.toFun i.1.castSucc stmtIn tr ∧
            stF.toFun i.1.succ stmtIn (tr.concat c)
        | ($ᵗ (pSpec.Challenge i))] ≤ (rbrSoundnessError i : ENNReal)) :
    Pr[ fun x => stF.toFun (Fin.last n) stmtIn x.1.1
      | do
        let s ← init
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (prover.runToRound (Fin.last n) stmtIn witIn)).run s]
      ≤ ((∑ i, rbrSoundnessError i : ℝ≥0) : ENNReal) :=
  probEvent_bind_le_of_forall_le fun s _ =>
    probEvent_stateFunction_run_le init impl stF witIn prover stmtIn hStmtIn hRbr s

/-- `probEvent_stateFunction_run_le` packaged against `rbrSoundnessWorstCase`: its state function
witnesses that no prover, from any initial oracle state, reaches a full transcript on which the
state function holds with probability more than the total round-by-round error.

What is still missing for `rbrSoundness_implies_soundness` is the last hop. `toFun_full` bounds the
verifier on a fresh oracle state drawn from `init`, whereas the soundness game hands the verifier
the state the prover left behind; for a stateful `impl` those are different distributions. -/
theorem rbrSoundnessWorstCase_probEvent_run_le
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0)
    (h : rbrSoundnessWorstCase init impl langIn langOut verifier rbrSoundnessError) :
    ∃ stF : verifier.StateFunction init impl langIn langOut,
      ∀ (stmtIn : StmtIn), stmtIn ∉ langIn →
      ∀ (WitIn' WitOut' : Type) (witIn : WitIn')
        (prover : Prover oSpec StmtIn WitIn' StmtOut WitOut' pSpec) (s : σ),
        Pr[ fun x => stF.toFun (Fin.last n) stmtIn x.1.1
          | (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
              (prover.runToRound (Fin.last n) stmtIn witIn)).run s]
          ≤ ((∑ i, rbrSoundnessError i : ℝ≥0) : ENNReal) := by
  obtain ⟨stF, hstF⟩ := h
  exact ⟨stF, fun stmtIn hStmtIn _ _ witIn prover s =>
    probEvent_stateFunction_run_le init impl stF witIn prover stmtIn hStmtIn
      (fun i tr => hstF stmtIn hStmtIn i tr) s⟩

/-- Round-by-round soundness with error `rbrSoundnessError` implies soundness with error
`∑ i, rbrSoundnessError i`, where the sum is over all rounds `i`. -/
theorem rbrSoundness_implies_soundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) :
      rbrSoundness init impl langIn langOut verifier rbrSoundnessError →
        soundness init impl langIn langOut verifier (∑ i, rbrSoundnessError i) := by sorry

/-- Round-by-round knowledge soundness with error `rbrKnowledgeError` implies round-by-round
soundness with the same error `rbrKnowledgeError`. -/
theorem rbrKnowledgeSoundness_implies_rbrSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : verifier.rbrKnowledgeSoundness init impl relIn relOut rbrKnowledgeError) :
    verifier.rbrSoundness init impl relIn.language relOut.language rbrKnowledgeError := by
  classical
  unfold rbrKnowledgeSoundness at h
  obtain ⟨WitMid, extractor, kSF, hkSF⟩ := h
  by_cases hWout : Nonempty WitOut
  · unfold rbrSoundness
    refine ⟨kSF.toStateFunction init impl, ?_⟩
    intro stmtIn hStmtIn WitIn' WitOut' witIn' prover i
    by_cases hWin : Nonempty WitIn
    · let prover' : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec :=
        { PrvState := prover.PrvState
          input := fun _ => prover.input (stmtIn, witIn')
          sendMessage := prover.sendMessage
          receiveChallenge := prover.receiveChallenge
          output := fun st => do
            let out ← prover.output st
            return (out.1, Classical.choice hWout) }
      have hrun : prover'.runToRound i.1.castSucc stmtIn (Classical.choice hWin) =
          prover.runToRound i.1.castSucc stmtIn witIn' := by rfl
      have hrunlog : prover'.runWithLogToRound i.1.castSucc stmtIn (Classical.choice hWin) =
          prover.runWithLogToRound i.1.castSucc stmtIn witIn' := by
        unfold Prover.runWithLogToRound
        rw [hrun]
      let logGame := do
        let s ← init
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover'.runWithLogToRound i.1.castSucc stmtIn (Classical.choice hWin)
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' s
      let plainGame := do
        let s ← init
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn'
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge))).run' s
      have hmap : (fun x => (x.1, x.2.1)) <$> logGame = plainGame := by
        simp [logGame, plainGame, ← Prover.runWithLogToRound_discard_log_eq_runToRound, hrunlog]
        rfl
      have hk := hkSF stmtIn (Classical.choice hWin) prover' i
      change probEvent plainGame (fun x =>
        ¬ (∃ w, kSF i.1.castSucc stmtIn x.1 w) ∧
          ∃ w, kSF i.1.succ stmtIn (x.1.concat x.2) w) ≤ _
      change probEvent logGame (fun x => ∃ w,
        ¬ kSF i.1.castSucc stmtIn x.1
            (extractor.extractMid i.1 stmtIn (x.1.concat x.2.1) w) ∧
          kSF i.1.succ stmtIn (x.1.concat x.2.1) w) ≤ _ at hk
      calc
        _ = probEvent logGame (fun x =>
            ¬ (∃ w, kSF i.1.castSucc stmtIn x.1 w) ∧
              ∃ w, kSF i.1.succ stmtIn (x.1.concat x.2.1) w) := by
              rw [← hmap, probEvent_map]
              rfl
        _ ≤ probEvent logGame (fun x => ∃ w,
            ¬ kSF i.1.castSucc stmtIn x.1
                (extractor.extractMid i.1 stmtIn (x.1.concat x.2.1) w) ∧
              kSF i.1.succ stmtIn (x.1.concat x.2.1) w) := by
              apply probEvent_mono
              intro x hx hbad
              obtain ⟨hprev, w, hnext⟩ := hbad
              exact ⟨w, fun hw => hprev ⟨_, hw⟩, hnext⟩
        _ ≤ _ := hk
    · let extractToInput : (m : Fin (n + 1)) → Transcript m pSpec → WitMid m → WitIn :=
        Fin.induction
          (fun tr w => cast extractor.eqIn w)
          (fun m ih tr w =>
            ih (Fin.init tr) (extractor.extractMid m stmtIn tr w))
      let plainGame := do
        let s ← init
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn'
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge))).run' s
      change probEvent plainGame (fun x =>
        ¬ (∃ w, kSF i.1.castSucc stmtIn x.1 w) ∧
          ∃ w, kSF i.1.succ stmtIn (x.1.concat x.2) w) ≤ _
      have hz : probEvent plainGame (fun x =>
          ¬ (∃ w, kSF i.1.castSucc stmtIn x.1 w) ∧
            ∃ w, kSF i.1.succ stmtIn (x.1.concat x.2) w) = 0 := by
        rw [probEvent_eq_zero_iff]
        intro x hx hbad
        obtain ⟨hprev, w, hnext⟩ := hbad
        exact hWin ⟨extractToInput i.1.succ (x.1.concat x.2) w⟩
      rw [hz]
      exact zero_le
  · have hLangOut : relOut.language = ∅ := by
      ext stmtOut
      simp only [Set.language, Set.mem_image, Prod.exists, exists_and_right,
        exists_eq_right, Set.mem_empty_iff_false, iff_false]
      intro hex
      exact hWout ⟨hex.choose⟩
    let sF : verifier.StateFunction init impl relIn.language relOut.language :=
      { toFun := fun m stmtIn _ => m = 0 ∧ stmtIn ∈ relIn.language
        toFun_empty := by
          intro stmtIn
          simp only [true_and]
        toFun_next := by
          intro m hdir stmtIn tr hfalse msg htrue
          exact Fin.succ_ne_zero m htrue.1
        toFun_full := by
          intro stmtIn tr hfalse
          rw [hLangOut]
          rw [probEvent_eq_zero_iff]
          simp only [Set.mem_empty_iff_false, not_false_eq_true, implies_true] }
    unfold rbrSoundness
    refine ⟨sF, ?_⟩
    intro stmtIn hStmtIn WitIn' WitOut' witIn' prover i
    let plainGame := do
      let s ← init
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn'
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge))).run' s
    change probEvent plainGame (fun x =>
      ¬ ((i.1.castSucc = 0) ∧ stmtIn ∈ relIn.language) ∧
        ((i.1.succ = 0) ∧ stmtIn ∈ relIn.language)) ≤ _
    have hz : probEvent plainGame (fun x =>
        ¬ ((i.1.castSucc = 0) ∧ stmtIn ∈ relIn.language) ∧
          ((i.1.succ = 0) ∧ stmtIn ∈ relIn.language)) = 0 := by
      rw [probEvent_eq_zero_iff]
      intro x hx hbad
      exact Fin.succ_ne_zero i.1 hbad.2.1
    rw [hz]
    exact zero_le

/-- Round-by-round knowledge soundness with error `rbrKnowledgeError` implies knowledge soundness
with error `∑ i, rbrKnowledgeError i`, where the sum is over all rounds `i`. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) :
      rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError →
        knowledgeSoundness init impl relIn relOut verifier (∑ i, rbrKnowledgeError i) := by sorry

-- /-- Round-by-round soundness for a protocol implies state-restoration soundness for the same
-- protocol with arbitrary added non-empty salts. -/
-- theorem rbrSoundness_implies_srSoundness_addSalt
--     {init : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id)}
--     {impl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp)}
--     (langIn : Set StmtIn) (langOut : Set StmtOut)
--     (verifier : Verifier oSpec StmtIn StmtOut pSpec)
--     (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0)
--     (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)] :
--       rbrSoundness init impl langIn langOut verifier rbrSoundnessError →
--         Verifier.StateRestoration.soundness init impl langIn langOut (verifier.addSalt Salt)
--           (∑ i, (rbrSoundnessError i)) := by sorry

-- /-- Round-by-round knowledge soundness for a protocol implies state-restoration
-- knowledge soundness for the same protocol with arbitrary added non-empty salts. -/
-- theorem rbrKnowledgeSoundness_implies_srKnowledgeSoundness_addSalt
--     {init : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id)}
--     {impl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp)}
--     (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
--     (verifier : Verifier oSpec StmtIn StmtOut pSpec)
--     (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0)
--     (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)] :
--       rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError →
--         Verifier.StateRestoration.knowledgeSoundness init impl relIn relOut
--           (verifier.addSalt Salt) (∑ i, rbrKnowledgeError i) := by sorry

/-- State-restoration soundness for a protocol with added salts implies state-restoration
soundness for the original protocol (with improved parameters?)
-/
theorem srSoundness_addSalt_implies_srSoundness_original
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)]
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (QueryImpl (srChallengeOracle StmtIn (pSpec.addSalt Salt)) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle StmtIn (pSpec.addSalt Salt)) Id) ProbComp))
    (srSoundnessError : ℝ≥0) :
      Verifier.StateRestoration.soundness srInit srImpl langIn langOut
        (verifier.addSalt Salt) srSoundnessError →
        Verifier.StateRestoration.soundness sorry sorry langIn langOut
          verifier srSoundnessError := by sorry

/-- State-restoration knowledge soundness for a protocol with added salts implies state-restoration
knowledge soundness for the original protocol with improved parameters. -/
theorem srKnowledgeSoundness_addSalt_implies_srKnowledgeSoundness_original
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)]
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (QueryImpl (srChallengeOracle StmtIn (pSpec.addSalt Salt)) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle StmtIn (pSpec.addSalt Salt)) Id) ProbComp))
    (srKnowledgeError : ℝ≥0) :
      Verifier.StateRestoration.knowledgeSoundness srInit srImpl relIn relOut
        (verifier.addSalt Salt) srKnowledgeError →
        Verifier.StateRestoration.knowledgeSoundness sorry sorry relIn relOut
          verifier srKnowledgeError := by sorry

/-- State-restoration soundness implies basic (straightline) soundness.

This theorem shows that state-restoration security is a strengthening of basic soundness.
The error is preserved in the implication. -/
theorem srSoundness_implies_soundness
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
    (srSoundnessError : ℝ≥0) :
      Verifier.StateRestoration.soundness srInit srImpl langIn langOut verifier srSoundnessError →
        soundness init impl langIn langOut verifier srSoundnessError := by
  sorry

/-- State-restoration knowledge soundness implies basic (straightline) knowledge soundness.

This theorem shows that state-restoration knowledge soundness is a strengthening of basic
knowledge soundness. The error is preserved in the implication. -/
theorem srKnowledgeSoundness_implies_knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
    (srKnowledgeError : ℝ≥0) :
      Verifier.StateRestoration.knowledgeSoundness srInit srImpl relIn relOut
        verifier srKnowledgeError →
      knowledgeSoundness init impl relIn relOut verifier srKnowledgeError := by sorry

-- TODO: state that round-by-round security implies state-restoration security for protocol with
-- arbitrary added (non-empty?) salts

-- TODO: state that state-restoration security for added salts imply state-restoration security for
-- the original protocol (with some better parameters)

-- TODO: state that state-restoration security implies basic security

end Implications

end Verifier

/-! ## Coordinate-wise special soundness generalizes special soundness

Both `Verifier.specialSound` (`Security.SpecialSoundness`) and
`Verifier.coordinateWiseSpecialSound` (`Security.CoordinateWiseSpecialSoundness`) are *defined* as
instances of the shape-generic `Verifier.treeSpecialSound`, differing only in the challenge-tree
shape they fix:

* plain special soundness fixes `distinctShape k` — arity `kᵢ`, node predicate `Function.Injective`
  (the `kᵢ` sibling challenges are pairwise distinct);
* CWSS fixes `D.toShape` — arity `ℓᵢ·(kᵢ-1)+1`, node predicate `IsSpecialSoundFamily ℓᵢ kᵢ`.

For the canonical `ℓᵢ = 1` structure `CWSSStructure.ofSpecialSound k` the two shapes are *equal*
(`toShape_ofSpecialSound_eq_distinctShape`): the arity is `kᵢ` and `IsSpecialSoundFamily 1 kᵢ`
reduces to injectivity (`CoordinateWise.isSpecialSoundFamily_one_iff_injective`). The bridge
`Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff` is then immediate from that shape
equality. -/

/-- Heterogeneous congruence for `Function.Injective`: injectivity transports across an equality of
the domain type together with a heterogeneous equality of the functions. -/
private theorem heq_injective {A A' β : Type} (h : A = A') {f : A → β} {g : A' → β}
    (hfg : HEq f g) : HEq (Function.Injective f) (Function.Injective g) := by
  subst h; obtain rfl := eq_of_heq hfg; exact HEq.rfl

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- The CWSS shape of the canonical `ℓᵢ = 1` structure `CWSSStructure.ofSpecialSound k` is exactly
the plain special-soundness shape `distinctShape k`. This is the structural heart of the equivalence
between CWSS and plain special soundness: both the arity (`1·(kᵢ-1)+1 = kᵢ`) and the node predicate
(`IsSpecialSoundFamily 1 kᵢ` vs. `Function.Injective`) agree. -/
theorem toShape_ofSpecialSound_eq_distinctShape (k : pSpec.ChallengeIdx → ℕ) (hk : ∀ i, 2 ≤ k i) :
    (CWSSStructure.ofSpecialSound k hk).toShape = distinctShape k := by
  have harity : (CWSSStructure.ofSpecialSound k hk).toShape.arity = (distinctShape k).arity := by
    funext i
    change 1 * (k i - 1) + 1 = k i
    have := hk i; omega
  refine ChallengeTreeShape.ext harity (Function.hfunext rfl (fun i i' hi => ?_))
  obtain rfl := eq_of_heq hi
  refine Function.hfunext (by rw [harity]) (fun c c' hc => ?_)
  refine HEq.trans (heq_of_eq (propext ?_)) (heq_injective (congrArg Fin (congrFun harity i)) hc)
  change CoordinateWise.IsSpecialSoundFamily 1 (k i)
      (fun j : Fin (1 * (k i - 1) + 1) =>
        (Equiv.funUnique (Fin 1) (pSpec.Challenge i)).symm (c j)) ↔ Function.Injective c
  rw [CoordinateWise.isSpecialSoundFamily_one_iff_injective]
  exact Equiv.comp_injective c (Equiv.funUnique (Fin 1) (pSpec.Challenge i)).symm

namespace Verifier

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Coordinate-wise special soundness generalizes special soundness.** Coordinate-wise special
soundness for the canonical `ℓᵢ = 1` structure `CWSSStructure.ofSpecialSound k` is *equivalent* to
plain `(k)`-special soundness for the same input and output relations. Both unfold to
`Verifier.treeSpecialSound` of a shape, and the two shapes are equal
(`toShape_ofSpecialSound_eq_distinctShape`), so the bridge is immediate. This is the
`coordinateWiseSpecialSound (ofSpecialSound k) ↔ specialSound k` bridge promised in
`Security.SpecialSoundness`: CWSS recovers `k`-special soundness in the single-coordinate case. -/
theorem coordinateWiseSpecialSound_ofSpecialSound_iff (k : pSpec.ChallengeIdx → ℕ)
    (hk : ∀ i, 2 ≤ k i)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) :
    verifier.coordinateWiseSpecialSound (WitOut := WitOut) init impl
      (CWSSStructure.ofSpecialSound k hk) relIn relOut
      ↔ verifier.specialSound init impl k relIn relOut := by
  unfold Verifier.coordinateWiseSpecialSound Verifier.specialSound
  rw [toShape_ofSpecialSound_eq_distinctShape]

end Verifier

namespace OracleVerifier

open ProtocolSpec

variable {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [∀ i, OracleInterface (OStmtOut i)]
  [∀ i, OracleInterface (pSpec.Message i)]

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Coordinate-wise special soundness vs. plain special soundness, oracle form.** The oracle-
reduction analogue of `Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff`, obtained by passing
to the underlying non-oracle verifier (both notions are defined via `OracleVerifier.toVerifier`). -/
theorem coordinateWiseSpecialSound_ofSpecialSound_iff (k : pSpec.ChallengeIdx → ℕ)
    (hk : ∀ i, 2 ≤ k i)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    verifier.coordinateWiseSpecialSound (WitOut := WitOut) init impl
      (CWSSStructure.ofSpecialSound k hk) relIn relOut
      ↔ verifier.specialSound init impl k relIn relOut :=
  Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff init impl k hk relIn relOut
    verifier.toVerifier

end OracleVerifier
