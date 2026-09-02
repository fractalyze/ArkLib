/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Composition.Sequential.HandlerCommutativity

/-!
# Drawing the challenges ahead of the run

`Prover.run` draws each challenge from the challenge oracle at the round that needs it. Some
arguments need them all in hand *before* the run starts -- notably composing knowledge soundness,
where the first component's adversary has to output a witness that only exists once the second
half has run, and a `Prover oSpec …` has no randomness of its own to run it with.

The two are equal in distribution: challenges are public coins, drawn independently of everything
else, so their position in the run is immaterial. This file supplies the pre-drawn vectors
(`ChalsBelow`), the handler that serves them (`chalImplBelow`), and the sampler
(`drawChalsBelow`).

Indices are `ℕ`-bounded (`(i : ℕ) < k`) rather than `Fin`-reindexed, unlike
`ProtocolSpec.ChallengesUpTo`: a round induction then extends the vector without ever
re-indexing the underlying `ChallengeIdx`, so the transports stay local to one `cast`.
-/

open OracleComp OracleSpec

namespace ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- The challenges of every round strictly before round `k`, supplied ahead of the run. -/
def ChalsBelow (pSpec : ProtocolSpec n) (k : ℕ) : Type :=
  ∀ i : pSpec.ChallengeIdx, (i.1 : ℕ) < k → pSpec.Challenge i

namespace ChalsBelow

/-- No round precedes round `0`. -/
def nil : pSpec.ChalsBelow 0 := fun _ h => absurd h (Nat.not_lt_zero _)

/-- Extend a pre-drawn vector by the challenge of round `k`. -/
def snoc {k : ℕ} {hk : k < n} (c : pSpec.ChalsBelow k)
    (h : pSpec.dir ⟨k, hk⟩ = .V_to_P) (x : pSpec.Challenge ⟨⟨k, hk⟩, h⟩) :
    pSpec.ChalsBelow (k + 1) :=
  fun i hi =>
    if hik : (i.1 : ℕ) < k then c i hik
    else cast (congrArg pSpec.Challenge
      (Subtype.ext (Fin.ext (show k = (i.1 : ℕ) by omega)))) x

/-- Extend a pre-drawn vector past a message round, which contributes no challenge. -/
def skip {k : ℕ} {hk : k < n} (c : pSpec.ChalsBelow k)
    (h : pSpec.dir ⟨k, hk⟩ = .P_to_V) : pSpec.ChalsBelow (k + 1) :=
  fun i hi =>
    if hik : (i.1 : ℕ) < k then c i hik
    else Direction.noConfusion (i.2.symm.trans
      ((congrArg pSpec.dir (Fin.ext (show (i.1 : ℕ) = k by omega))).trans h))

/-- Below the new round, an extended vector is the one it extends. -/
@[simp] lemma snoc_of_lt {k : ℕ} {hk : k < n} (c : pSpec.ChalsBelow k)
    (h : pSpec.dir ⟨k, hk⟩ = .V_to_P) (x : pSpec.Challenge ⟨⟨k, hk⟩, h⟩)
    (i : pSpec.ChallengeIdx) (hi : (i.1 : ℕ) < k + 1) (hik : (i.1 : ℕ) < k) :
    c.snoc h x i hi = c i hik := dif_pos hik

/-- At the new round, an extended vector is the challenge it was extended by. -/
@[simp] lemma snoc_self {k : ℕ} {hk : k < n} (c : pSpec.ChalsBelow k)
    (h : pSpec.dir ⟨k, hk⟩ = .V_to_P) (x : pSpec.Challenge ⟨⟨k, hk⟩, h⟩)
    (hi : ((⟨⟨k, hk⟩, h⟩ : pSpec.ChallengeIdx).1 : ℕ) < k + 1) :
    c.snoc h x ⟨⟨k, hk⟩, h⟩ hi = x := by
  rw [ChalsBelow.snoc, dif_neg (lt_irrefl k)]
  exact eq_of_heq (cast_heq _ x)

/-- Below the skipped round, an extended vector is the one it extends. -/
@[simp] lemma skip_of_lt {k : ℕ} {hk : k < n} (c : pSpec.ChalsBelow k)
    (h : pSpec.dir ⟨k, hk⟩ = .P_to_V) (i : pSpec.ChallengeIdx) (hi : (i.1 : ℕ) < k + 1)
    (hik : (i.1 : ℕ) < k) : c.skip h i hi = c i hik := dif_pos hik

end ChalsBelow

variable [∀ i, SampleableType (pSpec.Challenge i)]

/-- Sample the challenges of every round strictly before round `k`. -/
def drawChalsBelow (pSpec : ProtocolSpec n) [∀ i, SampleableType (pSpec.Challenge i)] :
    (k : ℕ) → k ≤ n → ProbComp (pSpec.ChalsBelow k)
  | 0, _ => pure ChalsBelow.nil
  | k + 1, hk => do
      let c ← drawChalsBelow pSpec k (by omega)
      match hd : pSpec.dir ⟨k, by omega⟩ with
      | .V_to_P => (fun x => c.snoc hd x) <$> ($ᵗ (pSpec.Challenge ⟨⟨k, by omega⟩, hd⟩))
      | .P_to_V => pure (c.skip hd)

/-- Serve the challenges of rounds before `k` from `c`, and sample the rest as usual. Rounds at or
after `k` are never reached by a run that stops at `k`, so the sampling branch is what makes the
handler total, not a fallback the run can observe. -/
def chalImplBelow {k : ℕ} (c : pSpec.ChalsBelow k) :
    QueryImpl ([pSpec.Challenge]ₒ'challengeOracleInterface) ProbComp :=
  fun q => if h : (q.1.1 : ℕ) < k then pure (c q.1 h) else $ᵗ (pSpec.Challenge q.1)

@[simp] lemma chalImplBelow_apply_of_lt {k : ℕ} (c : pSpec.ChalsBelow k)
    (q : ([pSpec.Challenge]ₒ'challengeOracleInterface).Domain) (h : (q.1.1 : ℕ) < k) :
    chalImplBelow c q = pure (c q.1 h) := dif_pos h

/-- `drawChalsBelow` one round on, at a challenge round. -/
theorem drawChalsBelow_succ_challenge {k : ℕ} (hk : k + 1 ≤ n)
    (hd : pSpec.dir ⟨k, by omega⟩ = .V_to_P) :
    pSpec.drawChalsBelow (k + 1) hk
      = pSpec.drawChalsBelow k (by omega) >>= fun c =>
          (fun x => c.snoc hd x) <$> ($ᵗ (pSpec.Challenge ⟨⟨k, by omega⟩, hd⟩)) := by
  rw [drawChalsBelow]
  refine bind_congr fun c => ?_
  split
  · rfl
  · rename_i hd'; exact Direction.noConfusion (hd.symm.trans hd')

/-- `drawChalsBelow` one round on, at a message round: nothing is drawn. -/
theorem drawChalsBelow_succ_message {k : ℕ} (hk : k + 1 ≤ n)
    (hd : pSpec.dir ⟨k, by omega⟩ = .P_to_V) :
    pSpec.drawChalsBelow (k + 1) hk
      = pSpec.drawChalsBelow k (by omega) >>= fun c => pure (c.skip hd) := by
  rw [drawChalsBelow]
  refine bind_congr fun c => ?_
  split
  · rename_i hd'; exact Direction.noConfusion (hd.symm.trans hd')
  · rfl

/-- Serve every challenge from a pre-drawn vector, in the base spec: no sampling at all. Total
because every round index is below `n`. -/
def chalImplFixed {ι : Type} {oSpec : OracleSpec ι} (c : pSpec.ChalsBelow n) :
    QueryImpl ([pSpec.Challenge]ₒ'challengeOracleInterface) (OracleComp oSpec) :=
  fun q => pure (c q.1 q.1.1.isLt)

@[simp] lemma chalImplBelow_apply_of_ge {k : ℕ} (c : pSpec.ChalsBelow k)
    (q : ([pSpec.Challenge]ₒ'challengeOracleInterface).Domain) (h : ¬ ((q.1.1 : ℕ) < k)) :
    chalImplBelow c q = $ᵗ (pSpec.Challenge q.1) := dif_neg h

@[simp] lemma chalImplBelow_nil : (chalImplBelow (ChalsBelow.nil (pSpec := pSpec)))
    = challengeQueryImpl := by
  funext q
  simp only [chalImplBelow, challengeQueryImpl]
  exact dif_neg (Nat.not_lt_zero _)


end ProtocolSpec

namespace Prover

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {S W S' W' : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- `liftTarget` into the monad a handler already lands in is the identity. -/
private lemma liftTarget_self {ι' : Type} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec' ProbComp) : QueryImpl.liftTarget ProbComp impl = impl := rfl

/-- Simulating a base-spec computation under an added handler ignores the added half. -/
private lemma simulateQ_addLift_base {ι' : Type} {spec' : OracleSpec ι'} {α : Type}
    (implP : QueryImpl oSpec ProbComp) (g : QueryImpl spec' ProbComp)
    (x : OracleComp oSpec α) :
    simulateQ (implP.addLift g : QueryImpl (oSpec + spec') ProbComp)
        (liftM x : OracleComp (oSpec + spec') α) = simulateQ implP x := by
  rw [QueryImpl.addLift_def, liftTarget_self, liftTarget_self, ← liftComp_eq_liftM,
    QueryImpl.simulateQ_add_liftComp_left]

/-- Simulating an added-spec computation under an added handler ignores the base half. -/
private lemma simulateQ_addLift_added {ι' : Type} {spec' : OracleSpec ι'} {α : Type}
    (implP : QueryImpl oSpec ProbComp) (g : QueryImpl spec' ProbComp)
    (y : OracleComp spec' α) :
    simulateQ (implP.addLift g : QueryImpl (oSpec + spec') ProbComp)
        (liftM y : OracleComp (oSpec + spec') α) = simulateQ g y := by
  rw [QueryImpl.addLift_def, liftTarget_self, liftTarget_self, ← liftComp_eq_liftM,
    QueryImpl.simulateQ_add_liftComp_right]

/-- **A partial run reaches only the challenges of the rounds it has run.** Two challenge handlers
agreeing on the rounds before `k` simulate `runToRound k` identically -- as computations, not just
in distribution. This is what lets a round induction extend the pre-drawn vector without
disturbing the prefix it has already accounted for. -/
theorem simulateQ_runToRound_congr (implP : QueryImpl oSpec ProbComp)
    (g₁ g₂ : QueryImpl ([pSpec.Challenge]ₒ'challengeOracleInterface) ProbComp)
    (Q : Prover oSpec S W S' W' pSpec) (stmt : S) (wit : W) :
    ∀ (k : ℕ) (_hk : k ≤ n),
      (∀ q, (q.1.1 : ℕ) < k → g₁ q = g₂ q) →
      simulateQ (implP.addLift g₁ : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
          (Q.runToRound ⟨k, by omega⟩ stmt wit)
        = simulateQ (implP.addLift g₂ : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
          (Q.runToRound ⟨k, by omega⟩ stmt wit) := by
  intro k
  induction k with
  | zero =>
    intro _ _
    rw [runToRound_mk_zero]
    simp
  | succ k ih =>
    intro hk hg
    rw [runToRound_mk_succ Q k (by omega)]
    unfold Prover.processRound
    refine Eq.trans (simulateQ_bind _ _ _) (Eq.trans ?_ (simulateQ_bind _ _ _).symm)
    refine Eq.trans (bind_congr fun p => ?_)
      (congrArg (fun A => A >>= _) (ih (by omega) fun q h => hg q (by omega)))
    obtain ⟨transcript, state⟩ := p
    dsimp only
    split
    · rename_i hDir
      refine Eq.trans (simulateQ_bind _ _ _) (Eq.trans ?_ (simulateQ_bind _ _ _).symm)
      refine Eq.trans (bind_congr fun _ => ?_)
        (congrArg (fun A => A >>= _) (Eq.trans (simulateQ_addLift_base _ _ _)
          (simulateQ_addLift_base _ _ _).symm))
      refine Eq.trans (simulateQ_bind _ _ _) (Eq.trans ?_ (simulateQ_bind _ _ _).symm)
      refine Eq.trans (bind_congr fun _ => ?_) (congrArg (fun A => A >>= _) ?_)
      · rfl
      · rw [ProtocolSpec.getChallenge, simulateQ_addLift_added, simulateQ_addLift_added]
        exact (simulateQ_spec_query (impl := g₁) _).trans
          ((hg ⟨⟨⟨k, by omega⟩, hDir⟩, ()⟩ (by simp)).trans
            (simulateQ_spec_query (impl := g₂) _).symm)
    · refine Eq.trans (simulateQ_bind _ _ _) (Eq.trans ?_ (simulateQ_bind _ _ _).symm)
      refine Eq.trans (bind_congr fun _ => ?_)
        (congrArg (fun A => A >>= _) (Eq.trans (simulateQ_addLift_base _ _ _)
          (simulateQ_addLift_base _ _ _).symm))
      rfl


/-- One round of a run, as a function of the state it starts from. `processRound` is exactly a
bind of this, which is what lets the round induction below talk about the round's body on its
own. -/
def roundBody (Q : Prover oSpec S W S' W' pSpec) (j : Fin n)
    (p : pSpec.Transcript j.castSucc × Q.PrvState j.castSucc) :
    OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Transcript j.succ × Q.PrvState j.succ) :=
  match hDir : pSpec.dir j with
  | .V_to_P => do
      let update ← Q.receiveChallenge ⟨j, hDir⟩ p.2
      let challenge ← pSpec.getChallenge ⟨j, hDir⟩
      return ⟨p.1.concat challenge, update challenge⟩
  | .P_to_V => do
      let ⟨msg, newState⟩ ← Q.sendMessage ⟨j, hDir⟩ p.2
      return ⟨p.1.concat msg, newState⟩

theorem processRound_eq_bind (Q : Prover oSpec S W S' W' pSpec) (j : Fin n)
    (X : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × Q.PrvState j.castSucc)) :
    Prover.processRound j Q X = X >>= roundBody Q j := rfl


/-- `roundBody` at a challenge round. -/
theorem roundBody_challenge (Q : Prover oSpec S W S' W' pSpec) (j : Fin n)
    (hd : pSpec.dir j = .V_to_P) (p : pSpec.Transcript j.castSucc × Q.PrvState j.castSucc) :
    Prover.roundBody Q j p = (do
      let update ← Q.receiveChallenge ⟨j, hd⟩ p.2
      let challenge ← pSpec.getChallenge ⟨j, hd⟩
      return ⟨p.1.concat challenge, update challenge⟩) := by
  unfold Prover.roundBody
  split
  · rfl
  · rename_i hd'; exact Direction.noConfusion (hd.symm.trans hd')

/-- `roundBody` at a message round. -/
theorem roundBody_message (Q : Prover oSpec S W S' W' pSpec) (j : Fin n)
    (hd : pSpec.dir j = .P_to_V) (p : pSpec.Transcript j.castSucc × Q.PrvState j.castSucc) :
    Prover.roundBody Q j p = (do
      let r ← Q.sendMessage ⟨j, hd⟩ p.2
      return ⟨p.1.concat r.1, r.2⟩) := by
  unfold Prover.roundBody
  split
  · rename_i hd'; exact Direction.noConfusion (hd.symm.trans hd')
  · rfl

/-- Simulating a challenge round: the prover's own step runs under `implP`, and the round's
challenge is whatever the challenge handler `g` returns for that round. -/
theorem simulateQ_roundBody_challenge (implP : QueryImpl oSpec ProbComp)
    (g : QueryImpl ([pSpec.Challenge]ₒ'challengeOracleInterface) ProbComp)
    (Q : Prover oSpec S W S' W' pSpec) (j : Fin n) (hd : pSpec.dir j = .V_to_P)
    (p : pSpec.Transcript j.castSucc × Q.PrvState j.castSucc) :
    simulateQ (implP.addLift g : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
        (Prover.roundBody Q j p)
      = simulateQ implP (Q.receiveChallenge ⟨j, hd⟩ p.2) >>= fun u =>
          g ⟨⟨j, hd⟩, ()⟩ >>= fun ch => (pure (p.1.concat ch, u ch) : ProbComp _) := by
  rw [roundBody_challenge Q j hd p]
  refine Eq.trans (simulateQ_bind _ _ _) ?_
  refine Eq.trans (congrArg (fun A => A >>= _) (simulateQ_addLift_base _ _ _)) ?_
  refine bind_congr fun u => ?_
  refine Eq.trans (simulateQ_bind _ _ _) ?_
  refine Eq.trans (congrArg (fun A => A >>= _)
    (Eq.trans (simulateQ_addLift_added _ _ _) (simulateQ_spec_query _ _))) ?_
  rfl

/-- Simulating a message round: no challenge is drawn, so the challenge handler is untouched. -/
theorem simulateQ_roundBody_message (implP : QueryImpl oSpec ProbComp)
    (g : QueryImpl ([pSpec.Challenge]ₒ'challengeOracleInterface) ProbComp)
    (Q : Prover oSpec S W S' W' pSpec) (j : Fin n) (hd : pSpec.dir j = .P_to_V)
    (p : pSpec.Transcript j.castSucc × Q.PrvState j.castSucc) :
    simulateQ (implP.addLift g : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
        (Prover.roundBody Q j p)
      = simulateQ implP (Q.sendMessage ⟨j, hd⟩ p.2) >>= fun r =>
          (pure (p.1.concat r.1, r.2) : ProbComp _) := by
  rw [roundBody_message Q j hd p]
  refine Eq.trans (simulateQ_bind _ _ _) ?_
  refine Eq.trans (congrArg (fun A => A >>= _) (simulateQ_addLift_base _ _ _)) ?_
  rfl


open OracleComp.DeferredSampling in
/-- Moving an independent draw from the innermost position of a bind chain to the front. -/
private lemma evalDist_pull {α β γ δ : Type} (A : ProbComp α) (R : α → ProbComp β)
    (C : ProbComp γ) (f : α → β → γ → δ) :
    𝒟[A >>= fun a => R a >>= fun b => C >>= fun c => (pure (f a b c) : ProbComp δ)]
      = 𝒟[C >>= fun c => A >>= fun a => R a >>= fun b => (pure (f a b c) : ProbComp δ)] :=
  (evalDist_bind_congr_left A _ _ fun a => evalDist_bind_comm (R a) C _).trans
    (evalDist_bind_comm A C _)

open OracleComp.DeferredSampling in
/-- Two computations with the same distribution have the same distribution after a common
continuation. -/
private lemma evalDist_bind_congr_prefix {α β : Type} {A B : ProbComp α} (h : 𝒟[A] = 𝒟[B])
    (K : α → ProbComp β) : 𝒟[A >>= K] = 𝒟[B >>= K] := by
  rw [evalDist_bind, evalDist_bind, h]

/-- **Run a prover with its challenges hardwired.** With the challenges supplied ahead of time the
run makes no challenge queries, so it is an ordinary `oSpec` computation -- which is what lets it
sit inside another prover's `output`, where only `oSpec` is available. -/
def runFixed (Q : Prover oSpec S W S' W' pSpec) (c : pSpec.ChalsBelow n) (stmt : S) (wit : W) :
    OracleComp oSpec (pSpec.FullTranscript × S' × W') :=
  simulateQ ((QueryImpl.id' oSpec).addLift (chalImplFixed (oSpec := oSpec) c) :
    QueryImpl (oSpec + [pSpec.Challenge]ₒ) (OracleComp oSpec)) (Q.run stmt wit)

section Eager

variable [∀ i, SampleableType (pSpec.Challenge i)]

/-- A hardwired run, simulated, is the run simulated with the challenges served from the same
vector. The bridge between `runFixed` and `evalDist_run_drawFirst`. -/
theorem simulateQ_runFixed (implP : QueryImpl oSpec ProbComp)
    (Q : Prover oSpec S W S' W' pSpec) (c : pSpec.ChalsBelow n) (stmt : S) (wit : W) :
    simulateQ implP (Q.runFixed c stmt wit)
      = simulateQ (implP.addLift (chalImplBelow c) :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp) (Q.run stmt wit) := by
  rw [runFixed, ← QueryImpl.simulateQ_compose]
  congr 1
  funext q
  rcases q with t | t
  · exact simulateQ_spec_query _ _
  · exact (chalImplBelow_apply_of_lt c t t.1.1.isLt).symm

open OracleComp.DeferredSampling in
/-- **The challenges may be drawn before the run.** Running with the challenge oracle live is
distributed like drawing every challenge of the first `k` rounds up front and serving those back.

The two differ only in *where* each draw happens, and a challenge draw is independent of everything
around it, so it commutes forward past the prover's own steps (`evalDist_bind_comm`). The induction
moves one round's draw at a time; `simulateQ_runToRound_congr` is what lets the prefix already
accounted for stay untouched. -/
theorem evalDist_runToRound_drawFirst (implP : QueryImpl oSpec ProbComp)
    (Q : Prover oSpec S W S' W' pSpec) (stmt : S) (wit : W) :
    ∀ (k : ℕ) (hk : k ≤ n),
      𝒟[simulateQ (implP.addLift challengeQueryImpl :
            QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
          (Q.runToRound ⟨k, by omega⟩ stmt wit)]
        = 𝒟[pSpec.drawChalsBelow k hk >>= fun c =>
              simulateQ (implP.addLift (chalImplBelow c) :
                  QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
                (Q.runToRound ⟨k, by omega⟩ stmt wit)] := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [show pSpec.drawChalsBelow 0 hk = pure ChalsBelow.nil from rfl, pure_bind,
      chalImplBelow_nil]
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    have hsplit : ∀ g : QueryImpl ([pSpec.Challenge]ₒ'challengeOracleInterface) ProbComp,
        simulateQ (implP.addLift g : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
            (Q.runToRound ⟨k, by omega⟩ stmt wit >>= Prover.roundBody Q ⟨k, hkn⟩)
          = simulateQ (implP.addLift g : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
              (Q.runToRound ⟨k, by omega⟩ stmt wit)
              >>= fun p => simulateQ (implP.addLift g :
                    QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
                  (Prover.roundBody Q ⟨k, hkn⟩ p) := fun g => simulateQ_bind _ _ _
    have hloc : ∀ (c : pSpec.ChalsBelow (k + 1)) (c₀ : pSpec.ChalsBelow k),
        (∀ (i : pSpec.ChallengeIdx) (hi : (i.1 : ℕ) < k + 1) (hi₀ : (i.1 : ℕ) < k),
            c i hi = c₀ i hi₀) →
        simulateQ (implP.addLift (chalImplBelow c) :
              QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
            (Q.runToRound ⟨k, by omega⟩ stmt wit)
          = simulateQ (implP.addLift (chalImplBelow c₀) :
                QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
              (Q.runToRound ⟨k, by omega⟩ stmt wit) := by
      intro c c₀ hcc
      refine simulateQ_runToRound_congr implP _ _ Q stmt wit k (by omega) fun q hq => ?_
      rw [chalImplBelow_apply_of_lt _ _ (by omega), chalImplBelow_apply_of_lt _ _ hq, hcc]
    rw [runToRound_mk_succ Q k hkn, processRound_eq_bind]
    cases hd : pSpec.dir ⟨k, hkn⟩ with
    | P_to_V =>
      have hR : (pSpec.drawChalsBelow (k + 1) hk >>= fun c' =>
            simulateQ (implP.addLift (chalImplBelow c') :
                QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
              (Q.runToRound ⟨k, by omega⟩ stmt wit >>= Prover.roundBody Q ⟨k, hkn⟩))
          = (pSpec.drawChalsBelow k (by omega) >>= fun c =>
              simulateQ (implP.addLift (chalImplBelow c) :
                  QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
                (Q.runToRound ⟨k, by omega⟩ stmt wit))
              >>= fun p : pSpec.Transcript (Fin.mk k hkn).castSucc ×
                    Q.PrvState (Fin.mk k hkn).castSucc =>
                  simulateQ implP (Q.sendMessage ⟨⟨k, hkn⟩, hd⟩ p.2)
                    >>= fun r => (pure (p.1.concat r.1, r.2) : ProbComp _) := by
        rw [drawChalsBelow_succ_message hk hd, bind_assoc, bind_assoc]
        refine bind_congr fun c => ?_
        rw [pure_bind, hsplit,
          hloc (c.skip hd) c fun i hi hi₀ => ChalsBelow.skip_of_lt c hd i hi hi₀]
        exact bind_congr fun p => simulateQ_roundBody_message implP _ Q ⟨k, hkn⟩ hd p
      refine Eq.trans (congrArg evalDist (hsplit challengeQueryImpl))
        (Eq.trans ?_ (congrArg evalDist hR).symm)
      refine Eq.trans (congrArg evalDist (bind_congr fun p =>
        simulateQ_roundBody_message implP _ Q ⟨k, hkn⟩ hd p)) ?_
      exact evalDist_bind_congr_prefix (ih (by omega)) _
    | V_to_P =>
      have hR : (pSpec.drawChalsBelow (k + 1) hk >>= fun c' =>
            simulateQ (implP.addLift (chalImplBelow c') :
                QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
              (Q.runToRound ⟨k, by omega⟩ stmt wit >>= Prover.roundBody Q ⟨k, hkn⟩))
          = pSpec.drawChalsBelow k (by omega) >>= fun c =>
              ($ᵗ (pSpec.Challenge ⟨⟨k, hkn⟩, hd⟩)) >>= fun x =>
                simulateQ (implP.addLift (chalImplBelow c) :
                    QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
                  (Q.runToRound ⟨k, by omega⟩ stmt wit)
                  >>= fun p : pSpec.Transcript (Fin.mk k hkn).castSucc ×
                        Q.PrvState (Fin.mk k hkn).castSucc =>
                      simulateQ implP (Q.receiveChallenge ⟨⟨k, hkn⟩, hd⟩ p.2)
                        >>= fun u => (pure (p.1.concat x, u x) : ProbComp _) := by
        rw [drawChalsBelow_succ_challenge hk hd, bind_assoc]
        refine bind_congr fun c => ?_
        rw [bind_map_left]
        refine bind_congr fun x => ?_
        rw [hsplit, hloc _ c fun i hi hi₀ => ChalsBelow.snoc_of_lt c hd x i hi hi₀]
        refine bind_congr fun p => ?_
        rw [simulateQ_roundBody_challenge implP _ Q ⟨k, hkn⟩ hd p,
          chalImplBelow_apply_of_lt _ _ (Nat.lt_succ_self k), ChalsBelow.snoc_self]
        exact bind_congr fun u => pure_bind _ _
      have hL : ∀ p, simulateQ (implP.addLift challengeQueryImpl :
              QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
            (Prover.roundBody Q ⟨k, hkn⟩ p)
          = simulateQ implP (Q.receiveChallenge ⟨⟨k, hkn⟩, hd⟩ p.2) >>= fun u =>
              ($ᵗ (pSpec.Challenge ⟨⟨k, hkn⟩, hd⟩)) >>= fun ch =>
                (pure (p.1.concat ch, u ch) : ProbComp _) :=
        fun p => simulateQ_roundBody_challenge implP _ Q ⟨k, hkn⟩ hd p
      refine Eq.trans (congrArg evalDist (hsplit challengeQueryImpl))
        (Eq.trans ?_ (congrArg evalDist hR).symm)
      refine Eq.trans (congrArg evalDist (bind_congr fun p => hL p)) ?_
      refine Eq.trans (evalDist_bind_congr_prefix (ih (by omega)) _) ?_
      refine Eq.trans (congrArg evalDist (bind_assoc _ _ _)) ?_
      exact evalDist_bind_congr_left _ _ _ fun c => evalDist_pull _ _ _ _


open OracleComp.DeferredSampling in
/-- **The challenges may be drawn before the whole run**, `Prover.output` included. The output
step queries only the base spec, so it rides along untouched. -/
theorem evalDist_run_drawFirst (implP : QueryImpl oSpec ProbComp)
    (Q : Prover oSpec S W S' W' pSpec) (stmt : S) (wit : W) :
    𝒟[simulateQ (implP.addLift challengeQueryImpl :
          QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp) (Q.run stmt wit)]
      = 𝒟[pSpec.drawChalsBelow n le_rfl >>= fun c =>
            simulateQ (implP.addLift (chalImplBelow c) :
                QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp) (Q.run stmt wit)] := by
  have hrun : ∀ g : QueryImpl ([pSpec.Challenge]ₒ'challengeOracleInterface) ProbComp,
      simulateQ (implP.addLift g : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
          (Q.run stmt wit)
        = simulateQ (implP.addLift g : QueryImpl (oSpec + [pSpec.Challenge]ₒ) ProbComp)
            (Q.runToRound ⟨n, by omega⟩ stmt wit)
            >>= fun p => simulateQ implP (Q.output p.2) >>= fun o =>
                  (pure (p.1, o) : ProbComp _) := by
    intro g
    refine Eq.trans (simulateQ_bind _ _ _) (bind_congr fun p => ?_)
    refine Eq.trans (simulateQ_bind _ _ _) ?_
    exact congrArg (fun A => A >>= _) (simulateQ_addLift_base _ _ _)
  refine Eq.trans (congrArg evalDist (hrun challengeQueryImpl)) ?_
  refine Eq.trans ?_ (congrArg evalDist (bind_congr fun c => (hrun (chalImplBelow c)).symm))
  refine Eq.trans (evalDist_bind_congr_prefix
    (evalDist_runToRound_drawFirst implP Q stmt wit n le_rfl) _) ?_
  exact congrArg evalDist (bind_assoc _ _ _)

end Eager
