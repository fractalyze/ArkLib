/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendStateFunction
import ArkLib.OracleReduction.Composition.Sequential.SplitProver

/-!
# Sequential composition preserves round-by-round soundness

`Verifier.append_rbrSoundness_of_pure` proves it, for a deterministic first verifier and a
stateless handler; the unconditional statement in `Append.lean` stays admitted, for the reason
that theorem's docstring gives.

The round-by-round game is much smaller than the soundness game: it runs the prover to one round
and draws one challenge, and never runs the verifier. So there is no `OptionT`, no ordering between
prover and verifier, and no commutativity hypothesis -- only the adversary has to be taken apart,
into `Prover.takeLeft` and `Prover.dropLeft`.

* `Prover.rbrGame_inl` / `rbrGame_inr` do that, as equations between *computations*: at a challenge
  round of the first protocol the appended game is the first half's own game, lifted; past the cut
  it is the first half's full run followed by the second half's game. Everything else is a
  distributional consequence of these two.
* `ProtocolSpec.Transcript.fstUpTo_liftTranscript`, `fstFull_liftTranscriptR` and
  `heq_snd_liftTranscriptR` undo the transcript re-indexing those equations introduce, which is
  what lets the appended state function be read as the component ones.
* `OracleComp.probEvent_bind_run'_of_isStateless` moves a bound from an averaged `init` to a fixed
  state, as `Verifier.soundness_of_isStateless` does for plain soundness. The second half of an
  appended protocol starts from the state the first half left behind.
* `OracleComp.probEvent_simulateQ_run'_map` pushes the re-indexing map out of a simulated run at
  the level of the whole event probability -- see its docstring for why it cannot be done a step
  at a time.
-/

open OracleComp OracleSpec ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

namespace ProtocolSpec.Transcript

/-- Splitting off the left half undoes `liftTranscript`. -/
theorem fstUpTo_liftTranscript (v : ℕ) (hv : v ≤ m) (hvn : v ≤ m + n)
    (T : pSpec₁.Transcript ⟨v, by omega⟩) :
    fstUpTo (pSpec₂ := pSpec₂) v hv (k := ⟨v, by omega⟩) le_rfl
        (liftTranscript (pSpec₂ := pSpec₂) v hv hvn T) = T := by
  funext i
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

/-- Splitting off the whole left half undoes `liftTranscriptR`'s left argument. -/
theorem fstFull_liftTranscriptR (w : ℕ) (hw : w ≤ n) (T₁ : pSpec₁.FullTranscript)
    (T₂ : pSpec₂.Transcript ⟨w, by omega⟩) :
    fstFull (k := ⟨m + w, by omega⟩) (by simp) (liftTranscriptR (pSpec₁ := pSpec₁) w hw T₁ T₂)
      = T₁ := by
  funext i
  have hi : (i : ℕ) < m := i.isLt
  simp only [fstFull, liftTranscriptR, dif_pos hi]
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

/-- Splitting off the right half undoes `liftTranscriptR`'s right argument. The cuts are
`m + w - m` and `w`, equal but not definitionally so, hence `HEq`. -/
theorem heq_snd_liftTranscriptR (w : ℕ) (hw : w ≤ n) (T₁ : pSpec₁.FullTranscript)
    (T₂ : pSpec₂.Transcript ⟨w, by omega⟩) :
    HEq (Transcript.snd (k := ⟨m + w, by omega⟩) (liftTranscriptR (pSpec₁ := pSpec₁) w hw T₁ T₂))
      T₂ := by
  refine heq_of_apply_heq (b := ⟨w, by omega⟩) (Fin.ext (by simp)) fun i hia hib => ?_
  have hnot : ¬ (m + i < m) := by omega
  have hib' : i < w := hib
  have hidx : ∀ h : m + i - m < w, HEq (T₂ ⟨m + i - m, h⟩) (T₂ ⟨i, hib⟩) := fun h => by
    rw [show (⟨m + i - m, h⟩ : Fin w) = ⟨i, hib⟩ from Fin.ext (show m + i - m = i by omega)]
  simp only [Transcript.snd, liftTranscriptR, dif_neg hnot]
  exact (cast_heq _ _).trans ((cast_heq _ _).trans (hidx _))

end ProtocolSpec.Transcript

namespace OracleComp

variable {σ : Type} {init : ProbComp σ}

/-- **A stateless handler makes the initial state irrelevant.** Averaging over an `init` that is
actually sampled gives back the fixed-state probability, because the run's distribution does not
depend on the state at all. The round-by-round counterpart of
`Verifier.soundness_of_isStateless`, and stated about an arbitrary simulated computation rather
than about a security predicate: the bad-transition game runs only the prover and one challenge
draw, so there is no `OptionT` and nothing else to carry. -/
theorem probEvent_bind_run'_of_isStateless {ι' : Type} {spec : OracleSpec ι'} {α : Type}
    {impl : QueryImpl spec (StateT σ ProbComp)} (hst : impl.IsStateless)
    (hinit : Pr[⊥ | init] = 0) (c : OracleComp spec α) (p : α → Prop) (s : σ) :
    Pr[p | init >>= fun s₀ => (simulateQ impl c).run' s₀] = Pr[p | (simulateQ impl c).run' s] := by
  have hconst : ∀ s₀ : σ, (simulateQ impl c).run' s₀ = (simulateQ impl c).run' s := fun s₀ => by
    rw [QueryImpl.simulateQ_run'_of_isStateless hst, QueryImpl.simulateQ_run'_of_isStateless hst]
  simp only [hconst]
  rw [probEvent_bind_eq_tsum, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' hinit, one_mul]

/-- Pushing a `map` out of a simulated run, at the level of the whole event probability. Stated
this way on purpose: the appended game's map re-indexes a transcript, so the intermediate terms are
not type-correct at `instances` transparency and `rw` refuses to build a motive for them. Rewriting
the entire `Pr[..]`, whose type is `ℝ≥0∞`, never has that problem. -/
theorem probEvent_simulateQ_run'_map {ι' : Type} {spec : OracleSpec ι'} {α β : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (f : α → β) (c : OracleComp spec α) (s₀ : σ)
    (p : β → Prop) :
    Pr[p | (simulateQ impl (f <$> c)).run' s₀] = Pr[p ∘ f | (simulateQ impl c).run' s₀] := by
  rw [simulateQ_map, Reduction.stateT_run'_map, probEvent_map]

/-- A simulated run that starts with a phase, bounded phase by phase. The first phase's result and
the state it leaves are what the second phase is handed, so a bound uniform in both bounds the
whole. -/
theorem probEvent_bind_phase_le {ι' : Type} {spec : OracleSpec ι'} {α β : Type}
    {impl : QueryImpl spec (StateT σ ProbComp)} (A : OracleComp spec α) (g : α → OracleComp spec β)
    (p : β → Prop) {ε : ENNReal}
    (h : ∀ (a : α) (s : σ), Pr[p | (simulateQ impl (g a)).run' s] ≤ ε) :
    Pr[p | init >>= fun s₀ => (simulateQ impl (A >>= g)).run' s₀] ≤ ε := by
  have hb : ∀ s₀ : σ, (simulateQ impl (A >>= g)).run' s₀
      = (simulateQ impl A).run s₀ >>= fun q => (simulateQ impl (g q.1)).run' q.2 := fun s₀ => by
    rw [simulateQ_bind, Reduction.stateT_run'_eq, StateT.run_bind, map_bind]
    exact bind_congr fun q => (Reduction.stateT_run'_eq _ _).symm
  simp only [hb, ← bind_assoc]
  exact probEvent_bind_le_of_forall_le fun q _ => h q.1 q.2

end OracleComp

namespace Prover

variable {Wit₁ Wit₃ : Type}

/-- **The bad-transition game at a left-half challenge round, split.** Running the appended
adversary up to a round inside the first protocol and drawing that round's challenge is the first
half's own game, lifted: the transcript is re-indexed by `liftTranscript` and the challenge
transported along `challenge_append_inl`. No probability is involved -- this is an equation between
computations, and it is what lets the first component's hypothesis be applied verbatim. -/
theorem rbrGame_inl (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtOut : Stmt₂) (stmt : Stmt₁) (wit : Wit₁) (i₁ : pSpec₁.ChallengeIdx) :
    (do
      let ⟨transcript, _⟩ ←
        P.runToRound (ChallengeIdx.inl (pSpec₂ := pSpec₂) i₁).1.castSucc stmt wit
      let challenge ← liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inl i₁))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      return (transcript, challenge))
      = (fun q => (liftTranscript (pSpec₂ := pSpec₂) (i₁.1 : ℕ) i₁.1.isLt.le (by omega) q.1,
            cast (challenge_append_inl (pSpec₂ := pSpec₂) i₁).symm q.2)) <$>
          (liftM (do
            let ⟨transcript, _⟩ ← (P.takeLeft stmtOut).runToRound i₁.1.castSucc stmt wit
            let challenge ← liftComp (pSpec₁.getChallenge i₁) (oSpec + [pSpec₁.Challenge]ₒ)
            return (transcript, challenge)) :
              OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
  -- The round index is `⟨i₁, _⟩` definitionally, but `rw` matches syntactically.
  show (do
      let x ← P.runToRound (⟨(i₁.1 : ℕ), by omega⟩ : Fin (m + n + 1)) stmt wit
      let challenge ← liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inl i₁))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      return (x.1, challenge)) = _
  rw [takeLeft_runToRound P stmtOut stmt wit (i₁.1 : ℕ) i₁.1.isLt.le (by omega)]
  simp only [liftComp_eq_liftM, liftM_bind, liftM_pure, map_bind, bind_map_left, map_pure]
  rw [liftM_liftM_getChallenge_inl (pSpec₂ := pSpec₂) i₁]
  simp only [bind_map_left, cast_cast, cast_eq]
  rfl

/-- **The bad-transition game at a right-half challenge round, split.** Past the cut the appended
adversary's partial run is the first half's full run followed by the second half's partial run
(`Prover.dropLeft_runToRound`), so the game is the second half's own game at the state the cut left
behind, with the two transcripts combined by `liftTranscriptR`. -/
theorem rbrGame_inr (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtOut : Stmt₂) (stmt : Stmt₁) (wit : Wit₁) (i₂ : pSpec₂.ChallengeIdx) :
    (do
      let ⟨transcript, _⟩ ←
        P.runToRound (ChallengeIdx.inr (pSpec₁ := pSpec₁) i₂).1.castSucc stmt wit
      let challenge ← liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr i₂))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      return (transcript, challenge))
      = (do
          let p ← (liftM ((P.takeLeft stmtOut).runToRound (Fin.last m) stmt wit) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
          (fun q => (liftTranscriptR (pSpec₁ := pSpec₁) (i₂.1 : ℕ) i₂.1.isLt.le p.1 q.1,
              cast (challenge_append_inr (pSpec₁ := pSpec₁) i₂).symm q.2)) <$>
            (liftM (do
              let ⟨transcript, _⟩ ← (P.dropLeft (Stmt₂ := Stmt₂)).runToRound i₂.1.castSucc stmtOut
                (cast (takeLeft_prvState_cut P stmtOut) p.2)
              let challenge ← liftComp (pSpec₂.getChallenge i₂) (oSpec + [pSpec₂.Challenge]ₒ)
              return (transcript, challenge)) :
                OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) := by
  show (do
      let x ← P.runToRound (⟨m + (i₂.1 : ℕ), by omega⟩ : Fin (m + n + 1)) stmt wit
      let challenge ← liftComp ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr i₂))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      return (x.1, challenge)) = _
  rw [dropLeft_runToRound P stmtOut stmt wit (i₂.1 : ℕ) i₂.1.isLt.le]
  simp only [liftComp_eq_liftM, liftM_bind, liftM_pure, map_bind, map_pure,
    bind_assoc, pure_bind]
  refine bind_congr fun p => bind_congr fun q => ?_
  rw [liftM_liftM_getChallenge_inr (pSpec₁ := pSpec₁) i₂]
  simp only [bind_map_left, cast_cast, cast_eq]
  rfl

end Prover

namespace Verifier

open scoped NNReal

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}

section StateFunctionInl

variable {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
  {S₁ : V₁.StateFunction init impl lang₁ lang₂} {S₂ : V₂.StateFunction init impl lang₂ lang₃}
  {verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂}
  {hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩} {hsupp : (support init).Nonempty}

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- Before the cut the appended state function is the first component's, read off the lifted
transcript. -/
theorem append_toFun_liftTranscript (stmt : Stmt₁) (v : ℕ) (hv : v ≤ m)
    (T : pSpec₁.Transcript ⟨v, by omega⟩) :
    (StateFunction.append init impl V₁ V₂ S₁ S₂ verify hVerify hsupp).toFun
        ⟨v, by omega⟩ stmt (liftTranscript (pSpec₂ := pSpec₂) v hv (by omega) T)
      ↔ S₁ ⟨v, by omega⟩ stmt T := by
  show dite _ _ _ ↔ _
  rw [dif_pos (show ((⟨v, by omega⟩ : Fin (m + n + 1)) : ℕ) ≤ m from hv),
    Transcript.fstUpTo_liftTranscript v hv (by omega) T]

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- `append_toFun_liftTranscript` one round on, with the round's message appended. -/
theorem append_toFun_liftTranscript_concat (stmt : Stmt₁) (v : ℕ) (hv : v < m)
    (T : pSpec₁.Transcript ⟨v, by omega⟩) (msg : pSpec₁.«Type» ⟨v, hv⟩) :
    (StateFunction.append init impl V₁ V₂ S₁ S₂ verify hVerify hsupp).toFun
        ⟨v + 1, by omega⟩ stmt
        (Transcript.concat
          (cast (type_append_lt (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) v hv (by omega)).symm msg)
          (liftTranscript (pSpec₂ := pSpec₂) v hv.le (by omega) T))
      ↔ S₁ ⟨v + 1, by omega⟩ stmt (Transcript.concat msg T) := by
  rw [← liftTranscript_concat (pSpec₂ := pSpec₂) v hv (by omega) T msg]
  exact append_toFun_liftTranscript stmt (v + 1) hv (Transcript.concat msg T)

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- At the cut the appended state function is still the first component's, on the first half's
full transcript. -/
theorem append_toFun_liftTranscriptR_zero (stmt : Stmt₁)
    (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.Transcript ⟨0, by omega⟩) :
    (StateFunction.append init impl V₁ V₂ S₁ S₂ verify hVerify hsupp).toFun
        ⟨m + 0, by omega⟩ stmt (liftTranscriptR (pSpec₁ := pSpec₁) 0 (by omega) T₁ T₂)
      ↔ S₁ (Fin.last m) stmt T₁ := by
  show dite _ _ _ ↔ _
  rw [dif_pos (show m + 0 ≤ m from le_rfl)]
  refine StateFunction.congr_apply S₁ rfl stmt fun i hia hib => ?_
  have hi : i < m := hib
  simp only [Transcript.fstUpTo, liftTranscriptR, dif_pos hi]
  exact (cast_heq _ _).trans (cast_heq _ _)

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- Past the cut the appended state function is the second component's, on the statement the
deterministic first verifier reported, or else that statement already being good. -/
theorem append_toFun_liftTranscriptR (stmt : Stmt₁) (w : ℕ) (hw : w ≤ n) (hw₀ : 0 < w)
    (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.Transcript ⟨w, by omega⟩) :
    (StateFunction.append init impl V₁ V₂ S₁ S₂ verify hVerify hsupp).toFun
        ⟨m + w, by omega⟩ stmt (liftTranscriptR (pSpec₁ := pSpec₁) w hw T₁ T₂)
      ↔ (S₂ ⟨w, by omega⟩ (verify stmt T₁) T₂ ∨ verify stmt T₁ ∈ lang₂) := by
  show dite _ _ _ ↔ _
  rw [dif_neg (show ¬ (m + w ≤ m) by omega),
    Transcript.fstFull_liftTranscriptR w hw T₁ T₂]
  exact or_congr (StateFunction.congr_heq S₂ (Fin.ext (show m + w - m = w by omega)) _
    (Transcript.heq_snd_liftTranscriptR w hw T₁ T₂)) Iff.rfl

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- `append_toFun_liftTranscriptR` one round on, with the round's message appended. -/
theorem append_toFun_liftTranscriptR_concat (stmt : Stmt₁) (w : ℕ) (hw : w < n)
    (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.Transcript ⟨w, by omega⟩)
    (msg : pSpec₂.«Type» ⟨w, hw⟩) :
    (StateFunction.append init impl V₁ V₂ S₁ S₂ verify hVerify hsupp).toFun
        ⟨m + w + 1, by omega⟩ stmt
        (Transcript.concat
          (cast (type_append_add (pSpec₁ := pSpec₁) w hw (by omega)).symm msg)
          (liftTranscriptR (pSpec₁ := pSpec₁) w hw.le T₁ T₂))
      ↔ (S₂ ⟨w + 1, by omega⟩ (verify stmt T₁) (Transcript.concat msg T₂)
          ∨ verify stmt T₁ ∈ lang₂) := by
  rw [← liftTranscriptR_concat (pSpec₁ := pSpec₁) w hw T₁ T₂ msg]
  exact append_toFun_liftTranscriptR stmt (w + 1) hw (by omega) T₁ (Transcript.concat msg T₂)

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **What a false appended state function says past the cut.** At the cut itself it says the first
component's state function is false at its last round, which for a deterministic first verifier
means the statement it reported is outside `lang₂` and so the second component's state function is
false at round zero. Past the cut it says both directly, because of the disjunct. Either way the
second component's bad-transition event is entered on a statement it is allowed to speak about. -/
theorem not_append_toFun_liftTranscriptR (stmt : Stmt₁) (w : ℕ) (hw : w ≤ n)
    (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.Transcript ⟨w, by omega⟩)
    (h : ¬ (StateFunction.append init impl V₁ V₂ S₁ S₂ verify hVerify hsupp).toFun
        ⟨m + w, by omega⟩ stmt (liftTranscriptR (pSpec₁ := pSpec₁) w hw T₁ T₂)) :
    verify stmt T₁ ∉ lang₂ ∧ ¬ S₂ ⟨w, by omega⟩ (verify stmt T₁) T₂ := by
  rcases Nat.eq_zero_or_pos w with hw₀ | hw₀
  · subst hw₀
    rw [append_toFun_liftTranscriptR_zero (hsupp := hsupp) stmt T₁ T₂] at h
    have hnot := StateFunction.not_mem_of_pure S₁ verify hVerify hsupp stmt T₁ h
    exact ⟨hnot, fun hc => hnot ((S₂.toFun_empty _).mpr
      ((StateFunction.congr_apply S₂ (b := 0) rfl _
        fun i hia _ => absurd hia (Nat.not_lt_zero i)).mp hc))⟩
  · rw [append_toFun_liftTranscriptR (hsupp := hsupp) stmt w hw hw₀ T₁ T₂, not_or] at h
    exact ⟨h.2, h.1⟩

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- The other half of the bad transition: past the cut a *true* appended state function is the
second component's, once the statement reported at the cut is known to be outside `lang₂`. -/
theorem append_toFun_liftTranscriptR_concat_of_not_mem (stmt : Stmt₁) (w : ℕ) (hw : w < n)
    (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.Transcript ⟨w, by omega⟩)
    (msg : pSpec₂.«Type» ⟨w, hw⟩) (hmem : verify stmt T₁ ∉ lang₂)
    (h : (StateFunction.append init impl V₁ V₂ S₁ S₂ verify hVerify hsupp).toFun
        ⟨m + w + 1, by omega⟩ stmt
        (Transcript.concat
          (cast (type_append_add (pSpec₁ := pSpec₁) w hw (by omega)).symm msg)
          (liftTranscriptR (pSpec₁ := pSpec₁) w hw.le T₁ T₂))) :
    S₂ ⟨w + 1, by omega⟩ (verify stmt T₁) (Transcript.concat msg T₂) :=
  ((append_toFun_liftTranscriptR_concat (hsupp := hsupp) stmt w hw T₁ T₂ msg).mp h).resolve_right
    hmem

end StateFunctionInl

/-- `Pr[⊥ | init] = 0` says `init` produces a seed. -/
theorem support_nonempty_of_probFailure_eq_zero (hinit : Pr[⊥ | init] = 0) :
    (support init).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  rw [probFailure_eq_one hcon] at hinit
  exact one_ne_zero hinit

/-- **Sequential composition preserves round-by-round soundness**, for a deterministic first
verifier and a stateless handler.

Four hypotheses beyond the statement admitted in `Append.lean`:

* `verify` / `hVerify` -- `V₁` is deterministic. The composed state function has to name the
  intermediate statement at every round past the cut, and a randomized `V₁` does not give one as a
  function of the transcript. The same hypothesis
  `Verifier.append_knowledgeSoundness_of_logIndependent` settled on.
* `hst` -- the handler is stateless. The second half's game starts from the state the first half
  left behind, while `h₂` is stated from `init`.
* `hinit` -- `init` is actually sampled. That is what turns `S₁`'s `toFun_full` into the set-level
  fact the boundary round reads, and what makes the fixed-state transfer above lossless.
* `Nonempty Stmt₂` -- `Prover.takeLeft` has to report an output statement. It plays no role in the
  game, which never calls a prover's `output`, but the type has to be inhabited for the split-off
  prover to be written down at all.

The two challenge regions are bounded separately. Inside the first protocol the appended game *is*
the first half's game (`Prover.rbrGame_inl`) and the appended state function *is* `S₁`
(`append_toFun_liftTranscript`), so `h₁` applies verbatim. Past the cut the run splits into the
first half's full run and the second half's game (`Prover.rbrGame_inr`), and for each first-half
transcript either the statement it reports is already in `lang₂` -- and the appended state
function's disjunct makes the bad-transition event empty -- or it is not, and the event is `V₂`'s,
bounded by `h₂`. -/
theorem append_rbrSoundness_of_pure [Nonempty Stmt₂]
    (hst : impl.IsStateless) (hinit : Pr[⊥ | init] = 0)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrSoundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.rbrSoundness init impl lang₂ lang₃ ε₂) :
      (V₁.append V₂).rbrSoundness init impl lang₁ lang₃
        (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  obtain ⟨S₁, hS₁⟩ := h₁
  obtain ⟨S₂, hS₂⟩ := h₂
  refine ⟨StateFunction.append init impl V₁ V₂ S₁ S₂ verify hVerify
    (support_nonempty_of_probFailure_eq_zero hinit), ?_⟩
  intro stmt hstmt WitIn WitOut witIn P i
  obtain ⟨stmtOut⟩ := ‹Nonempty Stmt₂›
  by_cases hlt : ((i.1 : Fin (m + n)) : ℕ) < m
  · -- The challenge round lies inside the first protocol.
    obtain ⟨i₁, rfl⟩ : ∃ i₁ : pSpec₁.ChallengeIdx, i = ChallengeIdx.inl i₁ :=
      ⟨⟨⟨(i.1 : ℕ), hlt⟩, by
          rw [← dir_append_lt (pSpec₂ := pSpec₂) (i.1 : ℕ) hlt i.1.isLt]; exact i.2⟩,
        Subtype.ext (Fin.ext rfl)⟩
    simp only [Function.comp_apply, ChallengeIdx.sumEquiv_symm_inl, Sum.elim_inl]
    rw [Prover.rbrGame_inl P stmtOut stmt witIn i₁]
    refine le_of_eq_of_le (Reduction.probEvent_bind_congr init fun s₀ => ?_)
      (hS₁ stmt hstmt WitIn _ witIn (P.takeLeft stmtOut) i₁)
    rw [probEvent_simulateQ_run'_map]
    refine Eq.trans (probEvent_of_evalDist_eq (Reduction.evalDist_stateT_run'_congr
      (Reduction.evalDist_simulateQ_liftM_left _ s₀)) _) ?_
    refine congrArg _ (funext fun q => propext (and_congr (not_congr ?_) ?_))
    · exact append_toFun_liftTranscript stmt (i₁.1 : ℕ) i₁.1.isLt.le q.1
    · exact append_toFun_liftTranscript_concat stmt (i₁.1 : ℕ) i₁.1.isLt q.1 q.2
  · -- The challenge round lies in the second protocol.
    obtain ⟨i₂, rfl⟩ : ∃ i₂ : pSpec₂.ChallengeIdx, i = ChallengeIdx.inr i₂ :=
      ⟨⟨⟨(i.1 : ℕ) - m, by omega⟩, by
          rw [← dir_append_ge (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (i.1 : ℕ) (by omega) i.1.isLt]
          exact i.2⟩,
        Subtype.ext (Fin.ext (show (i.1 : ℕ) = m + ((i.1 : ℕ) - m) by omega))⟩
    simp only [Function.comp_apply, ChallengeIdx.sumEquiv_symm_inr, Sum.elim_inr]
    rw [Prover.rbrGame_inr P stmtOut stmt witIn i₂]
    refine probEvent_bind_phase_le _ _ _ fun p s₁ => ?_
    rw [probEvent_simulateQ_run'_map]
    refine le_of_eq_of_le (probEvent_of_evalDist_eq (Reduction.evalDist_stateT_run'_congr
      (Reduction.evalDist_simulateQ_liftM_right _ s₁)) _) ?_
    by_cases hmem : verify stmt p.1 ∈ lang₂
    · -- The first half was broken, so the appended state function is already true: no transition.
      refine le_trans (probEvent_mono'' (q := fun _ => False) fun q hq =>
        absurd hmem (not_append_toFun_liftTranscriptR stmt (i₂.1 : ℕ) i₂.1.isLt.le p.1 q.1 hq.1).1)
        ?_
      simp
    · refine le_trans (probEvent_mono''
        (q := fun x : pSpec₂.Transcript i₂.1.castSucc × pSpec₂.Challenge i₂ =>
          ¬ S₂ i₂.1.castSucc (verify stmt p.1) x.1 ∧
            S₂ i₂.1.succ (verify stmt p.1) (Transcript.concat x.2 x.1))
        fun q hq => ⟨(not_append_toFun_liftTranscriptR stmt (i₂.1 : ℕ) i₂.1.isLt.le p.1 q.1 hq.1).2,
          append_toFun_liftTranscriptR_concat_of_not_mem stmt (i₂.1 : ℕ) i₂.1.isLt p.1 q.1 q.2
            hmem hq.2⟩) ?_
      rw [← probEvent_bind_run'_of_isStateless (hst.addLift challengeQueryImpl) hinit _ _ s₁]
      exact hS₂ (verify stmt p.1) hmem _ _ _ P.dropLeft i₂

end Verifier