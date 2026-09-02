/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendStateFunction
import ArkLib.OracleReduction.Composition.Sequential.SplitProver

/-!
# Groundwork for round-by-round soundness of a sequential composition

`Verifier.append_rbrSoundness` is still admitted in `Append.lean`. This file collects the pieces
its proof needs, each proved on its own.

The round-by-round game is much smaller than the soundness game: it runs the prover to one round
and draws one challenge, and never runs the verifier. So there is no `OptionT`, no ordering
between prover and verifier, and no commutativity hypothesis -- only the adversary has to be taken
apart, into `Prover.takeLeft` and `Prover.dropLeft`.

* `Prover.rbrGame_inl` / `rbrGame_inr` do that, as equations between *computations*: at a challenge
  round of the first protocol the appended game is the first half's own game, lifted; past the cut
  it is the first half's full run followed by the second half's game. Everything downstream is a
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

/-- `Pr[⊥ | init] = 0` says `init` produces a seed. -/
theorem support_nonempty_of_probFailure_eq_zero (hinit : Pr[⊥ | init] = 0) :
    (support init).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  rw [probFailure_eq_one hcon] at hinit
  exact one_ne_zero hinit

end Verifier
