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

end Prover
