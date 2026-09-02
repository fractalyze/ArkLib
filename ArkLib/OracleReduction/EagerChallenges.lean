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
