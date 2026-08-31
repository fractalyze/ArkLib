/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.ProtocolSpec.SeqCompose
import ArkLib.OracleReduction.Security.RoundByRound

/-!
  # The Appended Prover, and How It Runs

  This file defines `Prover.append` -- the prover of the sequential composition of two reductions --
  and characterizes its execution.

  It is split out of `Composition/Sequential/Append.lean`, which defines the appended verifier and
  reduction and states their security properties. The reason for the split is size: characterizing
  `Prover.append` takes far more material than defining it, because the definition cannot be
  unfolded usefully (see the note on `Fin.append` below), so every field needs a computation rule of
  its own before any proof about a run can proceed.

  The contents, in order:

  - `Prover.append` itself.
  - Computation rules for each of its fields, in all three regions of the round index -- before the
    boundary round `m`, at it, and after it -- plus both cases of `output` and the rule for `input`.
    Together these fully characterize the definition.
  - The round induction over `Prover.runToRound` that those rules feed, and the transcript
    bookkeeping it carries along (`ProtocolSpec.liftTranscript` / `liftTranscriptR`, in
    `ProtocolSpec/SeqCompose.lean`).
  - `Prover.append_run`, the statement that the appended prover runs `P₁` and then `P₂`.
-/

open OracleComp OracleSpec SubSpec

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/--
Appending two provers corresponding to two reductions, where the output statement & witness type for
the first prover is equal to the input statement & witness type for the second prover. We also
require a verifier for the first protocol in order to derive the intermediate statement for the
second prover.

This is defined by combining the two provers' private states and functions, with the exception that
the last private state of the first prover is "merged" into the first private state of the second
prover (via outputting the new statement and witness, and then inputting these into the second
prover). -/
def Prover.append (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) :
      Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where

  /- The combined prover's states are the concatenation of the first prover's states and the second
  prover's states (except the first one). -/
  PrvState := Fin.append (m := m + 1) P₁.PrvState (Fin.tail P₂.PrvState) ∘ Fin.cast (by omega)

  /- The combined prover's input function is the first prover's input function, except for when the
  first protocol is empty, in which case it is the second prover's input function -/
  input := fun ctxIn => by simp; exact P₁.input ctxIn

  /- The combined prover sends messages according to the round index `i` as follows:
  - if `i < m`, then it sends the message & updates the state as the first prover
  - if `i = m`, then it sends the message as the first prover, but further returns the beginning
    state of the second prover
  - if `i > m`, then it sends the message & updates the state as the second prover. -/
  sendMessage := fun ⟨i, hDir⟩ state => by
    dsimp [Fin.vappend_eq_append, Fin.append, Fin.addCases, Fin.tail,
      Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at hDir state ⊢
    by_cases hi : i < m
    · haveI : i < m + 1 := by omega
      simp [hi, Fin.vappend_left_of_lt] at hDir ⊢
      simp [this] at state
      exact P₁.sendMessage ⟨⟨i, hi⟩, hDir⟩ state
    · by_cases hi' : i = m
      · simp [hi', Fin.vappend_right_of_not_lt] at hDir state ⊢
        exact (do
          let ctxIn₂ ← P₁.output state
          letI state₂ := P₂.input ctxIn₂
          P₂.sendMessage ⟨⟨0, by omega⟩, hDir⟩ state₂)
      · haveI hi1 : ¬ i < m + 1 := by omega
        haveI hi2 : i - (m + 1) + 1 = i - m := by omega
        simp [hi, Fin.vappend_right_of_not_lt] at hDir ⊢
        simp [hi1] at state
        exact P₂.sendMessage ⟨⟨i - m, by omega⟩, hDir⟩ (dcast (by simp [hi2]) state)

  /- Receiving challenges is implemented essentially the same as sending messages, modulo the
  difference in direction. -/
  receiveChallenge := fun ⟨i, hDir⟩ state => by
    dsimp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.tail,
      Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at hDir state ⊢
    by_cases hi : i < m
    · haveI : i < m + 1 := by omega
      simp [hi, Fin.vappend_left_of_lt] at hDir ⊢
      simp [this] at state
      exact P₁.receiveChallenge ⟨⟨i, hi⟩, hDir⟩ state
    · by_cases hi' : i = m
      · simp [hi', Fin.vappend_right_of_not_lt] at hDir state ⊢
        exact (do
          let ctxIn₂ ← P₁.output state
          letI state₂ := P₂.input ctxIn₂
          P₂.receiveChallenge ⟨⟨0, by omega⟩, hDir⟩ state₂)
      · haveI hi1 : ¬ i < m + 1 := by omega
        haveI hi2 : i - (m + 1) + 1 = i - m := by omega
        simp [hi, Fin.vappend_right_of_not_lt] at hDir ⊢
        simp [hi1] at state
        exact P₂.receiveChallenge ⟨⟨i - m, by omega⟩, hDir⟩ (dcast (by simp [hi2]) state)

  /- The combined prover's output function has two cases:
  - if the second protocol is empty, then it is the composition of the first prover's output
    function, the second prover's input function, and the second prover's output function.
  - if the second protocol is non-empty, then it is the second prover's output function. -/
  output := fun state => by
    dsimp [Fin.append, Fin.addCases, Fin.tail, Fin.cast, Fin.last, Fin.subNat] at state
    by_cases hn : n = 0
    · simp [hn] at state
      exact (do
        let ctxIn₂ ← P₁.output state
        letI state₂ := P₂.input ctxIn₂
        P₂.output (dcast (by simp [hn]) state₂))
    · haveI : m + n - (m + 1) + 1 = n := by omega
      simp [hn] at state
      exact P₂.output (dcast (by simp [this, Fin.last]) state)

section Execution

namespace Prover

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
    {stmt : Stmt₁} {wit : Wit₁}

/-! ### Computation rules for `Prover.append`'s fields

`Prover.append`'s state family is `Fin.append P₁.PrvState (Fin.tail P₂.PrvState) ∘ Fin.cast _`.
`Fin.append` branches on `i < m` via `Fin.addCases`, which does **not** reduce for a variable
index -- `rfl` proves the state equation at a literal index and fails at a variable one. That is
why each field of `Prover.append` is built by `by_cases`/`simp`/`dcast` rather than by
computation, and why a proof about it cannot simply unfold.

The lemmas below are the interface that replaces unfolding: they transport the state family across
the two injections, and then compute each field at a left-injected index in one rewrite. Together
with the challenge-oracle lemmas in `ProtocolSpec/SeqCompose.lean`
(`liftM_getChallenge_append_inl` / `_inr`, proved by `rfl`) they are what an induction proving
`append_run` runs on.

Every field is now covered, in all three regions -- before the boundary, at it, and after it --
plus both cases of `output`. So `Prover.append` is fully characterized: any proof about it can
proceed by rewriting rather than by unfolding. What remains for `append_run` is the round induction
itself, over `Prover.runToRound`, together with the transcript bookkeeping. -/

/-- The appended prover's initial state is `P₁`'s. -/
theorem append_prvState_zero : (P₁.append P₂).PrvState 0 = P₁.PrvState 0 := by
  simp [Prover.append, Fin.append, Fin.addCases, Fin.cast, Fin.castLT]

/-- The appended prover initializes exactly as `P₁` does. The base case of a round induction. -/
theorem append_input (x : Stmt₁ × Wit₁) :
    (P₁.append P₂).input x
      = cast (append_prvState_zero (P₁ := P₁) (P₂ := P₂)).symm (P₁.input x) := by
  unfold Prover.append
  simp only [id_eq, eq_mpr_eq_cast, eq_mp_eq_cast]

/-- Transport of the appended state family at a left-injected round, before the round. -/
theorem prvState_castSucc_inl (i : Fin m) :
    (P₁.append P₂).PrvState (Fin.castAdd n i).castSucc = P₁.PrvState i.castSucc := by
  simp [Prover.append, Fin.append, Fin.addCases, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.cast,
    Fin.castLT]

/-- Transport of the appended state family at a left-injected round, after the round. -/
theorem prvState_succ_inl (i : Fin m) :
    (P₁.append P₂).PrvState (Fin.castAdd n i).succ = P₁.PrvState i.succ := by
  simp [Prover.append, Fin.append, Fin.addCases, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.cast,
    Fin.castLT, Fin.succ]

/-- Transport of the appended state family at a right-injected round, before the round.

The hypothesis `j ≠ 0` excludes the boundary round `m`, whose state before the round still belongs
to `P₁` -- that round is where `P₁.output` and `P₂.input` fire, and it is handled separately. -/
theorem prvState_castSucc_inr (j : Fin n) (hj : (j : ℕ) ≠ 0) :
    (P₁.append P₂).PrvState (Fin.natAdd m j).castSucc = P₂.PrvState j.castSucc := by
  have h1 : ¬ (m + (j : ℕ) < m + 1) := by omega
  simp [Prover.append, Fin.append, Fin.addCases, Fin.castSucc, Fin.natAdd, Fin.cast,
    Fin.castLT, Fin.tail, Fin.succ, h1]
  try (congr 1; apply Fin.ext; simp; omega)

/-- Transport of the appended state family at a right-injected round, after the round. -/
theorem prvState_succ_inr (j : Fin n) (hj : (j : ℕ) ≠ 0) :
    (P₁.append P₂).PrvState (Fin.natAdd m j).succ = P₂.PrvState j.succ := by
  have h1 : ¬ (m + (j : ℕ) + 1 < m + 1) := by omega
  simp [Prover.append, Fin.append, Fin.addCases, Fin.castSucc, Fin.natAdd, Fin.cast,
    Fin.castLT, Fin.tail, Fin.succ, h1]
  try (congr 1; apply Fin.ext; simp; omega)

/-- A `cast` between computations returning a pair is the pair of casts. Used to turn the transport
that `Prover.append`'s tactic-generated fields produce into the componentwise form the statements
below are phrased in. -/
private theorem cast_map_prod {ι' : Type} {spec : OracleSpec ι'} {A A' B B' : Type}
    (hA : A = A') (hB : B = B') (h : OracleComp spec (A × B) = OracleComp spec (A' × B'))
    (x : OracleComp spec (A × B)) :
    cast h x = (fun p => (cast hA p.1, cast hB p.2)) <$> x := by
  subst hA; subst hB; simp

/-- The arrow-valued counterpart of `cast_map_prod`, for `receiveChallenge`. -/
private theorem cast_map_arrow {ι' : Type} {spec : OracleSpec ι'} {A A' B B' : Type}
    (hA : A = A') (hB : B = B') (h : OracleComp spec (A → B) = OracleComp spec (A' → B'))
    (x : OracleComp spec (A → B)) :
    cast h x = (fun f a' => cast hB (f (cast hA.symm a'))) <$> x := by
  subst hA; subst hB; simp

/-- At a round strictly inside `pSpec₁`, the appended prover sends exactly `P₁`'s message and
updates exactly `P₁`'s state, modulo the transports. -/
theorem append_sendMessage_inl (i : MessageIdx pSpec₁)
    (st : (P₁.append P₂).PrvState (Fin.castAdd n i.1).castSucc) :
    (P₁.append P₂).sendMessage (MessageIdx.inl i) st
      = (fun p => (cast (message_append_inl i).symm p.1,
                   cast (prvState_succ_inl (P₁ := P₁) (P₂ := P₂) i.1).symm p.2))
        <$> P₁.sendMessage i (cast (prvState_castSucc_inl (P₁ := P₁) (P₂ := P₂) i.1) st) := by
  unfold Prover.append MessageIdx.inl
  simp only [Fin.is_lt, dif_pos, Fin.castAdd, Fin.castLE, id_eq, eq_mpr_eq_cast, eq_mp_eq_cast,
    Fin.eta]
  exact cast_map_prod _ _ _ _

/-- At a challenge round strictly inside `pSpec₁`, the appended prover receives exactly `P₁`'s
challenge and updates exactly `P₁`'s state, modulo the transports. -/
theorem append_receiveChallenge_inl (i : ChallengeIdx pSpec₁)
    (st : (P₁.append P₂).PrvState (Fin.castAdd n i.1).castSucc) :
    (P₁.append P₂).receiveChallenge (ChallengeIdx.inl i) st
      = (fun f c => cast (prvState_succ_inl (P₁ := P₁) (P₂ := P₂) i.1).symm
            (f (cast (challenge_append_inl (pSpec₂ := pSpec₂) i) c)))
        <$> P₁.receiveChallenge i (cast (prvState_castSucc_inl (P₁ := P₁) (P₂ := P₂) i.1) st) := by
  unfold Prover.append ChallengeIdx.inl
  simp only [Fin.is_lt, dif_pos, Fin.castAdd, Fin.castLE, id_eq, eq_mpr_eq_cast, eq_mp_eq_cast,
    Fin.eta]
  exact cast_map_arrow (challenge_append_inl (pSpec₂ := pSpec₂) i).symm
    (prvState_succ_inl (P₁ := P₁) (P₂ := P₂) i.1).symm _ _

/-- `append_sendMessage_inl` on the **raw** appended index. The `MessageIdx.inl` form above cannot
be `rw`-applied inside a round induction, whose goals carry `⟨v, _⟩` rather than
`MessageIdx.inl ⟨v, _⟩`: the two are definitionally equal but not syntactically, so unification
fails. Same reason the right-region rules below take the raw index. -/
theorem append_sendMessage_lt (i : MessageIdx (pSpec₁ ++ₚ pSpec₂))
    (hi : (i.1 : ℕ) < m) (hd : pSpec₁.dir ⟨(i.1 : ℕ), hi⟩ = .P_to_V)
    (st : (P₁.append P₂).PrvState i.1.castSucc)
    (hS : (P₁.append P₂).PrvState i.1.castSucc
            = P₁.PrvState (⟨(i.1 : ℕ), hi⟩ : Fin m).castSucc)
    (hM : pSpec₁.Message ⟨⟨(i.1 : ℕ), hi⟩, hd⟩ = (pSpec₁ ++ₚ pSpec₂).Message i)
    (hP : P₁.PrvState (⟨(i.1 : ℕ), hi⟩ : Fin m).succ
            = (P₁.append P₂).PrvState i.1.succ) :
    (P₁.append P₂).sendMessage i st
      = (fun p => (cast hM p.1, cast hP p.2))
        <$> P₁.sendMessage ⟨⟨(i.1 : ℕ), hi⟩, hd⟩ (cast hS st) := by
  obtain ⟨i, hDir⟩ := i
  unfold Prover.append
  simp only [hi, dif_pos, id_eq, eq_mpr_eq_cast, eq_mp_eq_cast, Fin.eta]
  refine (cast_map_prod hM hP _ _).trans ?_
  congr 1
  all_goals (congr 1; simp only [dcast_eq_root_cast, cast_cast]; rfl)

/-- `append_receiveChallenge_inl` on the raw appended index. See `append_sendMessage_lt`. -/
theorem append_receiveChallenge_lt (i : ChallengeIdx (pSpec₁ ++ₚ pSpec₂))
    (hi : (i.1 : ℕ) < m) (hd : pSpec₁.dir ⟨(i.1 : ℕ), hi⟩ = .V_to_P)
    (st : (P₁.append P₂).PrvState i.1.castSucc)
    (hS : (P₁.append P₂).PrvState i.1.castSucc
            = P₁.PrvState (⟨(i.1 : ℕ), hi⟩ : Fin m).castSucc)
    (hC : (pSpec₁ ++ₚ pSpec₂).Challenge i = pSpec₁.Challenge ⟨⟨(i.1 : ℕ), hi⟩, hd⟩)
    (hP : P₁.PrvState (⟨(i.1 : ℕ), hi⟩ : Fin m).succ
            = (P₁.append P₂).PrvState i.1.succ) :
    (P₁.append P₂).receiveChallenge i st
      = (fun f c => cast hP (f (cast hC c)))
        <$> P₁.receiveChallenge ⟨⟨(i.1 : ℕ), hi⟩, hd⟩ (cast hS st) := by
  obtain ⟨i, hDir⟩ := i
  unfold Prover.append
  simp only [hi, dif_pos, id_eq, eq_mpr_eq_cast, eq_mp_eq_cast, Fin.eta]
  refine (cast_map_arrow hC.symm hP _ _).trans ?_
  congr 1
  all_goals (congr 1; simp only [dcast_eq_root_cast, cast_cast]; rfl)

/-! The right region and the boundary are stated on the **raw** appended index rather than on a
right-injected one. That is deliberate: `Prover.append` produces the `pSpec₂` index as `i - m`, and
`i - m` does not rewrite to `j` under the dependent proofs carried by `Fin.mk`, so phrasing these on
`MessageIdx.inr j` leaves a normalization step that no `simp` set discharges. Taking `i` as the
parameter makes the two sides agree syntactically. -/

/-- At a round strictly after the boundary, the appended prover sends exactly `P₂`'s message. -/
theorem append_sendMessage_gt (i : MessageIdx (pSpec₁ ++ₚ pSpec₂))
    (hi : ¬ ((i.1 : ℕ) < m)) (hi' : (i.1 : ℕ) ≠ m)
    (hd : pSpec₂.dir ⟨(i.1 : ℕ) - m, by omega⟩ = .P_to_V)
    (st : (P₁.append P₂).PrvState i.1.castSucc)
    (hS : (P₁.append P₂).PrvState i.1.castSucc
            = P₂.PrvState (⟨(i.1 : ℕ) - m, by omega⟩ : Fin n).castSucc)
    (hM : pSpec₂.Message ⟨⟨(i.1 : ℕ) - m, by omega⟩, hd⟩
            = (pSpec₁ ++ₚ pSpec₂).Message i)
    (hP : P₂.PrvState (⟨(i.1 : ℕ) - m, by omega⟩ : Fin n).succ
            = (P₁.append P₂).PrvState i.1.succ) :
    (P₁.append P₂).sendMessage i st
      = (fun p => (cast hM p.1, cast hP p.2))
        <$> P₂.sendMessage ⟨⟨(i.1 : ℕ) - m, by omega⟩, hd⟩ (cast hS st) := by
  obtain ⟨i, hDir⟩ := i
  unfold Prover.append
  simp only [hi, hi', dif_neg, dite_false, id_eq, eq_mpr_eq_cast, eq_mp_eq_cast, Fin.eta]
  refine (cast_map_prod hM hP _ _).trans ?_
  congr 1
  all_goals (congr 1; simp only [dcast_eq_root_cast, cast_cast]; rfl)

/-- At a challenge round strictly after the boundary, the appended prover receives exactly `P₂`'s
challenge. -/
theorem append_receiveChallenge_gt (i : ChallengeIdx (pSpec₁ ++ₚ pSpec₂))
    (hi : ¬ ((i.1 : ℕ) < m)) (hi' : (i.1 : ℕ) ≠ m)
    (hd : pSpec₂.dir ⟨(i.1 : ℕ) - m, by omega⟩ = .V_to_P)
    (st : (P₁.append P₂).PrvState i.1.castSucc)
    (hS : (P₁.append P₂).PrvState i.1.castSucc
            = P₂.PrvState (⟨(i.1 : ℕ) - m, by omega⟩ : Fin n).castSucc)
    (hC : (pSpec₁ ++ₚ pSpec₂).Challenge i
            = pSpec₂.Challenge ⟨⟨(i.1 : ℕ) - m, by omega⟩, hd⟩)
    (hP : P₂.PrvState (⟨(i.1 : ℕ) - m, by omega⟩ : Fin n).succ
            = (P₁.append P₂).PrvState i.1.succ) :
    (P₁.append P₂).receiveChallenge i st
      = (fun f c => cast hP (f (cast hC c)))
        <$> P₂.receiveChallenge ⟨⟨(i.1 : ℕ) - m, by omega⟩, hd⟩ (cast hS st) := by
  obtain ⟨i, hDir⟩ := i
  unfold Prover.append
  simp only [hi, hi', dif_neg, dite_false, id_eq, eq_mpr_eq_cast, eq_mp_eq_cast, Fin.eta]
  refine (cast_map_arrow hC.symm hP _ _).trans ?_
  congr 1
  all_goals (congr 1; simp only [dcast_eq_root_cast, cast_cast]; rfl)

/-! The `_gt` rules above produce `P₂`'s round index as `i - m`, which is what `Prover.append`
literally builds. A right-region round induction, though, indexes by `m + w`: `m + (w + 1)` is
definitionally `(m + w) + 1`, while `(v + 1) - m` is not definitionally `(v - m) + 1`. The two forms
are propositionally but not definitionally equal, so the `_add` twins below do that one
normalization once, here, rather than at every step of the induction.

It cannot be done by rewriting inside the `_gt` statement: `⟨m + w - m, _⟩` sits in the index of
`pSpec₂.Message`, a type-dependent position. The `_idx_congr` helpers move across it instead, by
`subst`ing an equation of `MessageIdx`/`ChallengeIdx` -- which is available because the conclusion's
own type mentions only the *appended* index, the casts `hM`/`hP` having absorbed the component
one. -/

/-- Two equal message indices give the same `sendMessage`, once the results are transported to a
common type. The bridge from the `_gt` rules' `i - m` indexing to the `_add` rules' `m + w`. -/
private theorem sendMessage_idx_congr {N : ℕ} {pSpec : ProtocolSpec N} {S W S' W' : Type}
    (P : Prover oSpec S W S' W' pSpec) {i i' : MessageIdx pSpec} (h : i = i')
    {A B : Type} {st : P.PrvState i.1.castSucc} {st' : P.PrvState i'.1.castSucc}
    (hst : HEq st st')
    (hM : pSpec.Message i = A) (hM' : pSpec.Message i' = A)
    (hP : P.PrvState i.1.succ = B) (hP' : P.PrvState i'.1.succ = B) :
    (fun p => (cast hM p.1, cast hP p.2)) <$> P.sendMessage i st
      = (fun p => (cast hM' p.1, cast hP' p.2)) <$> P.sendMessage i' st' := by
  subst h
  cases hst
  rfl

/-- `sendMessage_idx_congr` for challenge rounds. -/
private theorem receiveChallenge_idx_congr {N : ℕ} {pSpec : ProtocolSpec N} {S W S' W' : Type}
    (P : Prover oSpec S W S' W' pSpec) {i i' : ChallengeIdx pSpec} (h : i = i')
    {A B : Type} {st : P.PrvState i.1.castSucc} {st' : P.PrvState i'.1.castSucc}
    (hst : HEq st st')
    (hC : A = pSpec.Challenge i) (hC' : A = pSpec.Challenge i')
    (hP : P.PrvState i.1.succ = B) (hP' : P.PrvState i'.1.succ = B) :
    (fun f c => cast hP (f (cast hC c))) <$> P.receiveChallenge i st
      = (fun f c => cast hP' (f (cast hC' c))) <$> P.receiveChallenge i' st' := by
  subst h
  cases hst
  rfl

/-- `append_sendMessage_gt` with the round written as `m + w`. See the note above for why this
indexing, and not `i - m`, is the one a right-region induction can run on. -/
theorem append_sendMessage_add (w : ℕ) (hw : w < n) (hw0 : 0 < w) (hmw : m + w < m + n)
    (hDirA : (pSpec₁ ++ₚ pSpec₂).dir ⟨m + w, hmw⟩ = .P_to_V)
    (hd : pSpec₂.dir ⟨w, hw⟩ = .P_to_V)
    (st : (P₁.append P₂).PrvState (⟨m + w, hmw⟩ : Fin (m + n)).castSucc)
    (hS : (P₁.append P₂).PrvState (⟨m + w, hmw⟩ : Fin (m + n)).castSucc
            = P₂.PrvState (⟨w, hw⟩ : Fin n).castSucc)
    (hM : pSpec₂.Message ⟨⟨w, hw⟩, hd⟩
            = (pSpec₁ ++ₚ pSpec₂).Message ⟨⟨m + w, hmw⟩, hDirA⟩)
    (hP : P₂.PrvState (⟨w, hw⟩ : Fin n).succ
            = (P₁.append P₂).PrvState (⟨m + w, hmw⟩ : Fin (m + n)).succ) :
    (P₁.append P₂).sendMessage ⟨⟨m + w, hmw⟩, hDirA⟩ st
      = (fun p => (cast hM p.1, cast hP p.2))
        <$> P₂.sendMessage ⟨⟨w, hw⟩, hd⟩ (cast hS st) := by
  have hidx : (⟨m + w - m, by omega⟩ : Fin n) = ⟨w, hw⟩ :=
    Fin.ext (by show m + w - m = w; omega)
  have hd' : pSpec₂.dir ⟨m + w - m, by omega⟩ = .P_to_V := by rw [hidx]; exact hd
  have hidxM : (⟨⟨m + w - m, by omega⟩, hd'⟩ : MessageIdx pSpec₂) = ⟨⟨w, hw⟩, hd⟩ :=
    Subtype.ext hidx
  have hS' : (P₁.append P₂).PrvState (⟨m + w, hmw⟩ : Fin (m + n)).castSucc
      = P₂.PrvState (⟨m + w - m, by omega⟩ : Fin n).castSucc := by rw [hidx]; exact hS
  have hM' : pSpec₂.Message ⟨⟨m + w - m, by omega⟩, hd'⟩
      = (pSpec₁ ++ₚ pSpec₂).Message ⟨⟨m + w, hmw⟩, hDirA⟩ := by rw [hidxM]; exact hM
  have hP' : P₂.PrvState (⟨m + w - m, by omega⟩ : Fin n).succ
      = (P₁.append P₂).PrvState (⟨m + w, hmw⟩ : Fin (m + n)).succ := by rw [hidx]; exact hP
  rw [append_sendMessage_gt (P₁ := P₁) (P₂ := P₂) ⟨⟨m + w, hmw⟩, hDirA⟩
        (by show ¬(m + w < m); omega) (by show m + w ≠ m; omega) hd' st hS' hM' hP']
  exact sendMessage_idx_congr P₂ hidxM ((cast_heq _ _).trans (cast_heq _ _).symm) hM' hM hP' hP

/-- `append_receiveChallenge_gt` with the round written as `m + w`. Dual to
`append_sendMessage_add`. -/
theorem append_receiveChallenge_add (w : ℕ) (hw : w < n) (hw0 : 0 < w) (hmw : m + w < m + n)
    (hDirA : (pSpec₁ ++ₚ pSpec₂).dir ⟨m + w, hmw⟩ = .V_to_P)
    (hd : pSpec₂.dir ⟨w, hw⟩ = .V_to_P)
    (st : (P₁.append P₂).PrvState (⟨m + w, hmw⟩ : Fin (m + n)).castSucc)
    (hS : (P₁.append P₂).PrvState (⟨m + w, hmw⟩ : Fin (m + n)).castSucc
            = P₂.PrvState (⟨w, hw⟩ : Fin n).castSucc)
    (hC : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨⟨m + w, hmw⟩, hDirA⟩
            = pSpec₂.Challenge ⟨⟨w, hw⟩, hd⟩)
    (hP : P₂.PrvState (⟨w, hw⟩ : Fin n).succ
            = (P₁.append P₂).PrvState (⟨m + w, hmw⟩ : Fin (m + n)).succ) :
    (P₁.append P₂).receiveChallenge ⟨⟨m + w, hmw⟩, hDirA⟩ st
      = (fun f c => cast hP (f (cast hC c)))
        <$> P₂.receiveChallenge ⟨⟨w, hw⟩, hd⟩ (cast hS st) := by
  have hidx : (⟨m + w - m, by omega⟩ : Fin n) = ⟨w, hw⟩ :=
    Fin.ext (by show m + w - m = w; omega)
  have hd' : pSpec₂.dir ⟨m + w - m, by omega⟩ = .V_to_P := by rw [hidx]; exact hd
  have hidxC : (⟨⟨m + w - m, by omega⟩, hd'⟩ : ChallengeIdx pSpec₂) = ⟨⟨w, hw⟩, hd⟩ :=
    Subtype.ext hidx
  have hS' : (P₁.append P₂).PrvState (⟨m + w, hmw⟩ : Fin (m + n)).castSucc
      = P₂.PrvState (⟨m + w - m, by omega⟩ : Fin n).castSucc := by rw [hidx]; exact hS
  have hC' : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨⟨m + w, hmw⟩, hDirA⟩
      = pSpec₂.Challenge ⟨⟨m + w - m, by omega⟩, hd'⟩ := by rw [hidxC]; exact hC
  have hP' : P₂.PrvState (⟨m + w - m, by omega⟩ : Fin n).succ
      = (P₁.append P₂).PrvState (⟨m + w, hmw⟩ : Fin (m + n)).succ := by rw [hidx]; exact hP
  rw [append_receiveChallenge_gt (P₁ := P₁) (P₂ := P₂) ⟨⟨m + w, hmw⟩, hDirA⟩
        (by show ¬(m + w < m); omega) (by show m + w ≠ m; omega) hd' st hS' hC' hP']
  exact receiveChallenge_idx_congr P₂ hidxC ((cast_heq _ _).trans (cast_heq _ _).symm)
    hC' hC hP' hP

/-- **The boundary round.** At round `m` the appended prover finishes `P₁` -- running `P₁.output`
and feeding the result through `P₂.input` -- and then takes `P₂`'s first round. This is the round
that makes `append_run` true rather than merely plausible: `P₁.output` fires exactly here, at the
same point in the sequence as it does on the right-hand side of that statement. -/
theorem append_sendMessage_boundary (hn : 0 < n) (i : MessageIdx (pSpec₁ ++ₚ pSpec₂))
    (hi : ¬ ((i.1 : ℕ) < m)) (hi' : (i.1 : ℕ) = m)
    (hd : pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    (st : (P₁.append P₂).PrvState i.1.castSucc)
    (hS : (P₁.append P₂).PrvState i.1.castSucc = P₁.PrvState (Fin.last m))
    (hM : pSpec₂.Message ⟨⟨0, hn⟩, hd⟩ = (pSpec₁ ++ₚ pSpec₂).Message i)
    (hP : P₂.PrvState (⟨0, hn⟩ : Fin n).succ = (P₁.append P₂).PrvState i.1.succ) :
    (P₁.append P₂).sendMessage i st
      = (fun p => (cast hM p.1, cast hP p.2)) <$>
          (do let ctx ← P₁.output (cast hS st)
              P₂.sendMessage ⟨⟨0, hn⟩, hd⟩ (P₂.input ctx)) := by
  obtain ⟨i, hDir⟩ := i
  have hb : (i : ℕ) = m := hi'
  unfold Prover.append
  simp only [hi, dif_neg, dite_false, dif_pos hb, id_eq, eq_mpr_eq_cast, eq_mp_eq_cast, Fin.eta]
  refine (cast_map_prod hM hP _ _).trans ?_
  congr 1
  all_goals (congr 1; simp only [dcast_eq_root_cast, cast_cast]; rfl)

/-- The boundary round, when it is a challenge round. Dual to `append_sendMessage_boundary`;
`P₁.output` and `P₂.input` fire here too, so exactly one of the two boundary lemmas applies. -/
theorem append_receiveChallenge_boundary (hn : 0 < n) (i : ChallengeIdx (pSpec₁ ++ₚ pSpec₂))
    (hi : ¬ ((i.1 : ℕ) < m)) (hi' : (i.1 : ℕ) = m)
    (hd : pSpec₂.dir ⟨0, hn⟩ = .V_to_P)
    (st : (P₁.append P₂).PrvState i.1.castSucc)
    (hS : (P₁.append P₂).PrvState i.1.castSucc = P₁.PrvState (Fin.last m))
    (hC : (pSpec₁ ++ₚ pSpec₂).Challenge i = pSpec₂.Challenge ⟨⟨0, hn⟩, hd⟩)
    (hP : P₂.PrvState (⟨0, hn⟩ : Fin n).succ = (P₁.append P₂).PrvState i.1.succ) :
    (P₁.append P₂).receiveChallenge i st
      = (fun f c => cast hP (f (cast hC c))) <$>
          (do let ctx ← P₁.output (cast hS st)
              P₂.receiveChallenge ⟨⟨0, hn⟩, hd⟩ (P₂.input ctx)) := by
  obtain ⟨i, hDir⟩ := i
  have hb : (i : ℕ) = m := hi'
  unfold Prover.append
  simp only [hi, dif_neg, dite_false, dif_pos hb, id_eq, eq_mpr_eq_cast, eq_mp_eq_cast, Fin.eta]
  refine (cast_map_arrow hC.symm hP _ _).trans ?_
  congr 1
  all_goals (congr 1; simp only [dcast_eq_root_cast, cast_cast]; rfl)

/-- When `pSpec₂` is non-empty, the appended prover's output is `P₂`'s: `P₁.output` already fired at
the boundary round. -/
theorem append_output_pos (hn : ¬ (n = 0))
    (st : (P₁.append P₂).PrvState (Fin.last (m + n)))
    (hS : (P₁.append P₂).PrvState (Fin.last (m + n)) = P₂.PrvState (Fin.last n)) :
    (P₁.append P₂).output st = P₂.output (cast hS st) := by
  unfold Prover.append
  simp only [hn, dif_neg, dite_false, id_eq, eq_mpr_eq_cast, eq_mp_eq_cast, Fin.eta]
  congr 1
  simp only [dcast_eq_root_cast, cast_cast]
  rfl

/-- When `pSpec₂` is empty there is no boundary round, so `output` is where `P₁.output`, `P₂.input`
and `P₂.output` all fire. Together with `append_output_pos` this is why `P₁.output` runs exactly
once regardless of `n`. -/
theorem append_output_zero (hn : n = 0)
    (st : (P₁.append P₂).PrvState (Fin.last (m + n)))
    (hS : (P₁.append P₂).PrvState (Fin.last (m + n)) = P₁.PrvState (Fin.last m))
    (hZ : P₂.PrvState 0 = P₂.PrvState (Fin.last n)) :
    (P₁.append P₂).output st
      = (do let ctx ← P₁.output (cast hS st)
            P₂.output (cast hZ (P₂.input ctx))) := by
  unfold Prover.append
  simp only [hn, dif_pos, dite_true, id_eq, eq_mpr_eq_cast, eq_mp_eq_cast, Fin.eta]
  congr 1
  all_goals (congr 1; simp only [dcast_eq_root_cast, cast_cast]; rfl)

-- The challenge-oracle inclusions that `append_run`'s statement lifts along are provided
-- (proved) by `ProtocolSpec.subSpec_challenge_append_left` / `..._right` in
-- `ProtocolSpec/SeqCompose.lean`, with their `LawfulSubSpec` instances and the `@[simp]` lemmas
-- `liftM_getChallenge_append_inl` / `_inr` that compute the lifted challenge query.
--
-- Scope of what lawfulness buys: `support_liftComp` / `mem_support_liftComp_iff` apply directly.
-- `evalDist_liftComp` / `probEvent_liftComp` do NOT apply at this shape — they additionally
-- require `IsUniformSpec` on both specs, and `oSpec` here is arbitrary. The security definitions
-- below measure after `simulateQ pImpl`, so relating the two sides at the distribution level will
-- need `simulateQ_liftM_eq_of_query` plus the fact that `challengeQueryImpl` for the appended
-- protocol, precomposed with the lift, agrees with `challengeQueryImpl` for the component — a
-- `SampleableType`-compatibility fact across the transport that is not yet proved.

/-- Transport of the appended state family at a left round index, in the `Fin (m + 1)` indexing
that a round induction uses (as opposed to the `Fin m` indexing of the field rules above). -/
theorem prvState_castAdd (i : Fin (m + 1)) :
    (P₁.append P₂).PrvState (Fin.cast (by omega) (Fin.castAdd n i)) = P₁.PrvState i := by
  simp [Prover.append, Fin.append, Fin.addCases, Fin.cast, Fin.castLT, Fin.castAdd, Fin.castLE]
  omega

/-! The two transports below are phrased on the **appended** index `k` with `k ≤ m`, rather than on
`Fin.cast _ (Fin.castAdd n i)`. That is the indexing `Fin.induction` actually produces on the
left-hand side, so stating them this way means the induction never has to rewrite its own index --
which it cannot do, since the transcript and state types both depend on it. -/

/-- State transport at an appended round index inside the left component. -/
theorem prvState_le (k : Fin (m + n + 1)) (hk : (k : ℕ) ≤ m) :
    (P₁.append P₂).PrvState k = P₁.PrvState ⟨k, by omega⟩ := by
  have hlt : (k : ℕ) < m + 1 := by omega
  simp [Prover.append, Fin.append, Fin.addCases, Fin.cast, Fin.castLT, hlt]

/-- Transcript transport at an appended round index inside the left component. -/
theorem transcript_le (k : Fin (m + n + 1)) (hk : (k : ℕ) ≤ m) :
    (pSpec₁ ++ₚ pSpec₂).Transcript k = pSpec₁.Transcript ⟨k, by omega⟩ := by
  show ((pSpec₁ ++ₚ pSpec₂).take _ _).FullTranscript = (pSpec₁.take _ _).FullTranscript
  rw [take_append_left_of_le hk]

/-- State transport at a raw `Fin.mk` index, the form a `Nat`-indexed round induction produces.
Pairs with `ProtocolSpec.liftTranscript` on the transcript side. -/
theorem prvState_lt' (v : ℕ) (hv : v ≤ m) (hvn : v ≤ m + n) :
    (P₁.append P₂).PrvState ⟨v, by omega⟩ = P₁.PrvState ⟨v, by omega⟩ := by
  have hlt : v < m + 1 := by omega
  simp [Prover.append, Fin.append, Fin.addCases, Fin.cast, Fin.castLT, hlt]

/-- State transport strictly after the boundary. At `v = m` the state is still `P₁`'s, which is why
this needs `m < v` rather than `m ≤ v`; that round is `append_sendMessage_boundary`'s. -/
theorem prvState_gt' (v : ℕ) (hm : m < v) (hvn : v ≤ m + n) :
    (P₁.append P₂).PrvState ⟨v, by omega⟩ = P₂.PrvState ⟨v - m, by omega⟩ := by
  have h1 : ¬ (v < m + 1) := by omega
  simp [Prover.append, Fin.append, Fin.addCases, Fin.cast, Fin.castLT, Fin.tail, Fin.succ, h1]
  try (congr 1; apply Fin.ext; simp; omega)

/-- `prvState_gt'` in the `m + w` indexing a right-region induction uses. Needs `0 < w` for the
same reason `prvState_gt'` needs `m < v`: at `w = 0` the state is still `P₁`'s. -/
theorem prvState_add (w : ℕ) (hw : w ≤ n) (hw0 : 0 < w) :
    (P₁.append P₂).PrvState ⟨m + w, by omega⟩ = P₂.PrvState ⟨w, by omega⟩ := by
  have h1 : ¬ (m + w < m + 1) := by omega
  simp [Prover.append, Fin.append, Fin.addCases, Fin.cast, Fin.castLT, Fin.tail, Fin.succ, h1]
  try (congr 1; apply Fin.ext; simp; omega)

/-- Unfold `runToRound` one round at a raw `Fin.mk` successor index.

`Fin.induction_succ` only fires on an index of the form `Fin.succ j`, and a round induction hands
you `⟨v + 1, _⟩` instead. The two are definitionally equal, so `show` bridges them -- but `rw`
cannot, because the motive is not type correct. -/
theorem runToRound_mk_succ {N : ℕ} {pSpec : ProtocolSpec N} {S W S' W' : Type}
    (P : Prover oSpec S W S' W' pSpec) (v : ℕ) (hv : v < N) (stmt : S) (wit : W) :
    P.runToRound ⟨v + 1, by omega⟩ stmt wit
      = Prover.processRound ⟨v, hv⟩ P (P.runToRound ⟨v, by omega⟩ stmt wit) := by
  show P.runToRound (Fin.succ ⟨v, hv⟩) stmt wit = _
  simp only [Prover.runToRound, Fin.induction_succ]
  rfl

/-- **Base case of the round induction.** Before any round has run, the appended prover's partial
run is `P₁`'s, transported. The appended index is written as `0` rather than as
`Fin.cast _ (Fin.castAdd n 0)` because the two are definitionally equal and `Fin.induction_zero`
only fires on the former; rewriting between them is blocked by a dependent motive, since the
transcript and state types both depend on the index. -/
theorem append_runToRound_zero (stmt : Stmt₁) (wit : Wit₁) :
    (P₁.append P₂).runToRound 0 stmt wit
      = (fun p => (cast (transcript_append_castAdd (pSpec₂ := pSpec₂) 0).symm p.1,
                   cast (prvState_castAdd (P₁ := P₁) (P₂ := P₂) 0).symm p.2))
        <$> liftM (P₁.runToRound 0 stmt wit) := by
  simp only [Prover.runToRound, Fin.induction_zero, Prover.append_input]
  simp only [ChallengeIdx, Challenge, liftM_pure]
  congr 1
  exact Prod.ext (Subsingleton.elim _ _) rfl

theorem runToRound_mk_zero {N : ℕ} {pSpec : ProtocolSpec N} {S W S' W' : Type}
    (P : Prover oSpec S W S' W' pSpec) (h : 0 < N + 1) (stmt : S) (wit : W) :
    P.runToRound ⟨0, h⟩ stmt wit = pure (default, P.input (stmt, wit)) := by
  show P.runToRound 0 stmt wit = _
  simp only [Prover.runToRound, Fin.induction_zero]
  rfl

theorem liftM_liftM_base {α : Type} (x : OracleComp oSpec α) :
    (liftM ((liftM x : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α)) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)
      = liftM x := by
  induction x using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t oa ih =>
    simp only [liftM_bind, ih]
    rfl

theorem map_bind_left {α β γ : Type} {ι' : Type} {spec : OracleSpec ι'}
    (f : α → β) (x : OracleComp spec α) (g : β → OracleComp spec γ) :
    (f <$> x) >>= g = x >>= fun a => g (f a) := by
  simp

theorem liftM_liftM_getChallenge_inl (i : ChallengeIdx pSpec₁) :
    (liftM ((liftM (pSpec₁.getChallenge i) :
            OracleComp (oSpec + [pSpec₁.Challenge]ₒ) (pSpec₁.Challenge i))) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (pSpec₁.Challenge i))
      = cast (challenge_append_inl (pSpec₂ := pSpec₂) i)
          <$> (liftM ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inl i)) :
                OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := rfl

/-- `liftM_liftM_base`'s right-region twin: a base-spec computation lifted through `pSpec₂`'s
challenge oracle and then into the appended one is the direct lift. Like the left version this is
not `rfl` -- the two lifts differ structurally at every query -- so it goes by induction. -/
theorem liftM_liftM_base_right {α : Type} (x : OracleComp oSpec α) :
    (liftM ((liftM x : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) α)) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)
      = liftM x := by
  induction x using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t oa ih =>
    simp only [liftM_bind, ih]
    rfl

/-- `liftM_liftM_getChallenge_inl`'s right-region twin. Unlike `liftM_liftM_base_right` this one
*is* `rfl`: both sides are the single query `ChallengeIdx.inr i` with the same response transport,
which is exactly what `liftM_challenge_append_inr` pins down. -/
theorem liftM_liftM_getChallenge_inr (i : ChallengeIdx pSpec₂) :
    (liftM ((liftM (pSpec₂.getChallenge i) :
            OracleComp (oSpec + [pSpec₂.Challenge]ₒ) (pSpec₂.Challenge i))) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (pSpec₂.Challenge i))
      = cast (challenge_append_inr (pSpec₁ := pSpec₁) i)
          <$> (liftM ((pSpec₁ ++ₚ pSpec₂).getChallenge (ChallengeIdx.inr i)) :
                OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := rfl

set_option maxHeartbeats 4000000 in
-- Rewriting each field rule drags a chain of casts through `Prover.append`'s `dcast`s; the
-- resulting defeq checks are large. Raised limit.
theorem append_processRound_lt (v : ℕ) (hv : v < m) (hvn : v < m + n)
    (X : OracleComp (oSpec + [pSpec₁.Challenge]ₒ)
          (pSpec₁.Transcript ⟨v, by omega⟩ × P₁.PrvState ⟨v, by omega⟩)) :
    Prover.processRound ⟨v, hvn⟩ (P₁.append P₂)
        ((fun p => (liftTranscript (pSpec₂ := pSpec₂) v (by omega) (by omega) p.1,
                    cast (Prover.prvState_lt' (P₁ := P₁) (P₂ := P₂)
                      v (by omega) (by omega)).symm p.2))
          <$> liftM X)
      = (fun p => (liftTranscript (pSpec₂ := pSpec₂) (v + 1) (by omega) (by omega) p.1,
                   cast (Prover.prvState_lt' (P₁ := P₁) (P₂ := P₂)
                     (v + 1) (by omega) (by omega)).symm p.2))
        <$> liftM (Prover.processRound ⟨v, hv⟩ P₁ X) := by
  unfold Prover.processRound
  simp only [map_bind, liftM_bind, bind_assoc, bind_map_left, Function.comp]
  refine bind_congr fun p => ?_
  have hdir : (pSpec₁ ++ₚ pSpec₂).dir ⟨v, hvn⟩ = pSpec₁.dir ⟨v, hv⟩ :=
    dir_append_lt (pSpec₂ := pSpec₂) v hv hvn
  split
  · rename_i hDirA
    split
    · rename_i hDirB
      rw [Prover.append_receiveChallenge_lt (hi := hv) (hd := hDirB)
        (hS := Prover.prvState_lt' v hv.le hvn.le)
        (hC := ProtocolSpec.type_append_lt v hv hvn)
        (hP := (Prover.prvState_lt' (v + 1) (by omega) (by omega)).symm)]
      simp only [liftM_map, liftM_bind, map_bind, bind_assoc, liftM_liftM_base,
        liftM_liftM_getChallenge_inl, bind_map_left, bind_pure_comp, cast_cast, cast_eq,
        Functor.map_map, Function.comp]
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
      simp only [liftM_bind, map_bind, bind_assoc, liftM_pure, map_pure, bind_pure_comp,
        Function.comp]
      rw [Prover.append_sendMessage_lt (hi := hv) (hd := hDirB)
        (hS := Prover.prvState_lt' v hv.le hvn.le)
        (hM := (ProtocolSpec.type_append_lt v hv hvn).symm)
        (hP := (Prover.prvState_lt' (v + 1) (by omega) (by omega)).symm)]
      simp only [liftM_map, liftM_liftM_base, cast_cast, cast_eq, Functor.map_map]
      congr 1
      funext x
      congr 1
      rw [liftTranscript_concat (pSpec₂ := pSpec₂) v hv hvn]


set_option maxHeartbeats 4000000 in
-- Each induction step re-elaborates `append_processRound_lt`'s statement, casts included.
-- Raised limit.
theorem append_runToRound_lt (stmt : Stmt₁) (wit : Wit₁) :
    ∀ (v : ℕ) (hv : v ≤ m) (hvn : v ≤ m + n),
    (P₁.append P₂).runToRound ⟨v, by omega⟩ stmt wit
      = (fun p => (liftTranscript (pSpec₂ := pSpec₂) v hv hvn p.1,
                   cast (Prover.prvState_lt' (P₁ := P₁) (P₂ := P₂) v hv hvn).symm p.2))
        <$> liftM (P₁.runToRound ⟨v, by omega⟩ stmt wit) := by
  intro v
  induction v with
  | zero =>
    intro hv hvn
    rw [runToRound_mk_zero, runToRound_mk_zero, Prover.append_input]
    simp only [ChallengeIdx, Challenge, liftM_pure]
    congr 1
    refine Prod.ext ?_ ?_
    · exact Subsingleton.elim _ _
    · rfl
  | succ v ih =>
    intro hv hvn
    rw [Prover.runToRound_mk_succ (P₁.append P₂) v (by omega),
        Prover.runToRound_mk_succ P₁ v (by omega),
        ih (by omega) (by omega)]
    exact append_processRound_lt v (by omega) (by omega) _

set_option maxHeartbeats 4000000 in
-- Same cast-chasing as `append_processRound_lt`, on the right region. Raised limit.
/-- `processRound` distributes over a bind in its input: it consumes the input with a single
`>>=`, so this is `bind_assoc`. The right-region induction needs it to reach past the `P₁` run and
the `P₁.output`/`P₂.input` handover that sit in front of `P₂`'s partial run. -/
theorem processRound_bind {N : ℕ} {pSpec : ProtocolSpec N} {S W S' W' α : Type}
    (j : Fin N) (P : Prover oSpec S W S' W' pSpec)
    (A : OracleComp (oSpec + [pSpec.Challenge]ₒ) α)
    (f : α → OracleComp (oSpec + [pSpec.Challenge]ₒ)
          (pSpec.Transcript j.castSucc × P.PrvState j.castSucc)) :
    Prover.processRound j P (A >>= f) = A >>= fun a => Prover.processRound j P (f a) := by
  unfold Prover.processRound
  rw [bind_assoc]

/-- Unfold `runToRound` at index `1`. Like `runToRound_mk_zero` / `runToRound_mk_succ` this is a
`show`-based defeq bridge: `Fin.induction_succ` fires on `Fin.succ ⟨0, _⟩` and a literal `1` is not
syntactically that. -/
theorem runToRound_mk_one {N : ℕ} {pSpec : ProtocolSpec N} {S W S' W' : Type}
    (P : Prover oSpec S W S' W' pSpec) (hN : 0 < N) (stmt : S) (wit : W) :
    P.runToRound ⟨1, by omega⟩ stmt wit = Prover.processRound ⟨0, hN⟩ P
      (pure ((default : pSpec.Transcript 0), P.input (stmt, wit))) := by
  change P.runToRound (Fin.succ ⟨0, hN⟩) stmt wit = _
  simp only [Prover.runToRound, Fin.induction_succ]
  rfl

/-- The right region's `processRound` commutation, the counterpart of `append_processRound_lt`.
Runs for `w ≥ 1`; `w = 0` is the boundary round, which is `append_processRound_boundary`. -/
theorem append_processRound_add (w : ℕ) (hw : w < n) (hw0 : 0 < w)
    (T₁ : pSpec₁.FullTranscript)
    (X : OracleComp (oSpec + [pSpec₂.Challenge]ₒ)
          (pSpec₂.Transcript ⟨w, by omega⟩ × P₂.PrvState ⟨w, by omega⟩)) :
    Prover.processRound ⟨m + w, by omega⟩ (P₁.append P₂)
        ((fun p => (liftTranscriptR (pSpec₁ := pSpec₁) w (by omega) T₁ p.1,
                    cast (Prover.prvState_add (P₁ := P₁) (P₂ := P₂) w (by omega) hw0).symm p.2))
          <$> liftM X)
      = (fun p => (liftTranscriptR (pSpec₁ := pSpec₁) (w + 1) (by omega) T₁ p.1,
                   cast (Prover.prvState_add (P₁ := P₁) (P₂ := P₂) (w + 1) (by omega)
                     (by omega)).symm p.2))
        <$> liftM (Prover.processRound ⟨w, hw⟩ P₂ X) := by
  unfold Prover.processRound
  simp only [map_bind, liftM_bind, bind_map_left]
  refine bind_congr fun p => ?_
  have hdir : (pSpec₁ ++ₚ pSpec₂).dir ⟨m + w, by omega⟩ = pSpec₂.dir ⟨w, hw⟩ :=
    dir_append_add (pSpec₁ := pSpec₁) w hw (by omega)
  split
  · rename_i hDirA
    split
    · rename_i hDirB
      rw [Prover.append_receiveChallenge_add (P₁ := P₁) (P₂ := P₂) w hw hw0 (by omega)
        hDirA hDirB _
        (hS := Prover.prvState_add w (by omega) hw0)
        (hC := ProtocolSpec.type_append_add w hw (by omega))
        (hP := (Prover.prvState_add (w + 1) (by omega) (by omega)).symm)]
      simp only [liftM_map, liftM_bind, map_bind, liftM_liftM_base_right,
        liftM_liftM_getChallenge_inr, bind_map_left, bind_pure_comp, cast_cast,
        Functor.map_map]
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
      simp only [bind_pure_comp]
      rw [Prover.append_sendMessage_add (P₁ := P₁) (P₂ := P₂) w hw hw0 (by omega)
        hDirA hDirB _
        (hS := Prover.prvState_add w (by omega) hw0)
        (hM := (ProtocolSpec.type_append_add w hw (by omega)).symm)
        (hP := (Prover.prvState_add (w + 1) (by omega) (by omega)).symm)]
      simp only [liftM_map, liftM_liftM_base_right, cast_cast, Functor.map_map]
      congr 1
      funext x
      congr 1
      rw [liftTranscriptR_concat (pSpec₁ := pSpec₁) w hw T₁]

set_option maxHeartbeats 4000000 in
-- Both sides carry `Prover.append`'s `dcast` chains through a two-sided direction split.
-- Raised limit.
/-- **The boundary round commutes.** Processing round `m` of the appended protocol, applied to the
left region's result, runs `P₁.output`, feeds it through `P₂.input`, and takes `P₂`'s first round --
in that order, and at the same point in the sequence as running `P₁` to completion and then starting
`P₂`. This is the step that makes `append_run` true, and it is true only because
`Prover.processRound` draws a round's challenge *after* the prover's own queries for that round; see
its docstring, and `headIsBase_append_run_eq_base` below. -/
theorem append_processRound_boundary (hn : 0 < n)
    (X : OracleComp (oSpec + [pSpec₁.Challenge]ₒ)
          (pSpec₁.Transcript ⟨m, by omega⟩ × P₁.PrvState ⟨m, by omega⟩)) :
    Prover.processRound ⟨m, by omega⟩ (P₁.append P₂)
        ((fun p => (liftTranscript (pSpec₂ := pSpec₂) m le_rfl (by omega) p.1,
                    cast (Prover.prvState_lt' (P₁ := P₁) (P₂ := P₂) m le_rfl (by omega)).symm p.2))
          <$> liftM X)
      = (do
          let p ← liftM X
          let ctx ← liftM (P₁.output p.2)
          let q ← liftM (Prover.processRound ⟨0, hn⟩ P₂
                    (pure ((default : pSpec₂.Transcript 0), P₂.input ctx)))
          return (liftTranscriptR (pSpec₁ := pSpec₁) 1 hn p.1 q.1,
                  cast (Prover.prvState_add (P₁ := P₁) (P₂ := P₂) 1 hn Nat.one_pos).symm q.2)) := by
  unfold Prover.processRound
  simp only [bind_map_left, pure_bind]
  refine bind_congr fun p => ?_
  have hdir : (pSpec₁ ++ₚ pSpec₂).dir ⟨m, by omega⟩ = pSpec₂.dir ⟨0, hn⟩ :=
    dir_append_add (pSpec₁ := pSpec₁) 0 hn (by omega)
  split
  · rename_i hDirA
    split
    · rename_i hDirB
      rw [Prover.append_receiveChallenge_boundary (P₁ := P₁) (P₂ := P₂) hn ⟨⟨m, by omega⟩, hDirA⟩
        (by change ¬(m < m); omega) rfl hDirB _
        (hS := Prover.prvState_lt' m le_rfl (by omega))
        (hC := ProtocolSpec.type_append_add 0 hn (by omega))
        (hP := (Prover.prvState_add 1 hn Nat.one_pos).symm)]
      simp only [liftM_map, liftM_bind, map_bind, bind_assoc,
        liftM_liftM_base_right, liftM_liftM_getChallenge_inr, bind_map_left, bind_pure_comp,
        cast_cast, Functor.map_map]
      refine bind_congr fun ctx => ?_
      refine bind_congr fun u => ?_
      congr 1
      funext ch
      rw [liftTranscriptR_one (pSpec₁ := pSpec₁) hn p.1]
      congr 2
      exact (eq_of_heq ((cast_heq _ _).trans (cast_heq _ ch))).symm
    · rename_i hDirB
      exact Direction.noConfusion ((hdir.symm.trans hDirA).symm.trans hDirB)
  · rename_i hDirA
    split
    · rename_i hDirB
      exact Direction.noConfusion ((hdir.symm.trans hDirA).symm.trans hDirB)
    · rename_i hDirB
      rw [Prover.append_sendMessage_boundary (P₁ := P₁) (P₂ := P₂) hn ⟨⟨m, by omega⟩, hDirA⟩
        (by change ¬(m < m); omega) rfl hDirB _
        (hS := Prover.prvState_lt' m le_rfl (by omega))
        (hM := (ProtocolSpec.type_append_add 0 hn (by omega)).symm)
        (hP := (Prover.prvState_add 1 hn Nat.one_pos).symm)]
      simp only [liftM_map, liftM_bind, map_bind, liftM_liftM_base_right,
        bind_pure_comp, cast_cast, Functor.map_map]
      refine bind_congr fun ctx => ?_
      congr 1
      funext x
      rw [liftTranscriptR_one (pSpec₁ := pSpec₁) hn p.1]
      rfl

set_option maxHeartbeats 4000000 in
-- The induction re-elaborates `append_processRound_add`'s statement, casts included,
-- at every step. Raised limit.
/-- **The right region's round induction.** After the boundary, the appended prover's partial run
is `P₁`'s full run, then the `P₁.output` / `P₂.input` handover, then `P₂`'s partial run -- with the
two transcripts combined by `liftTranscriptR` and the state transported by `prvState_add`.

This cannot be stated uniformly from `w = 0`: at the boundary round the appended prover's state is
still `P₁`'s and `P₁.output` has not fired, so the equation is false there. It runs from `w = 1`,
with `append_processRound_boundary` as its base case and `append_runToRound_lt` supplying the left
region. -/
theorem append_runToRound_ge (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n) :
    ∀ (w : ℕ) (hw : w ≤ n) (hw0 : 0 < w),
    (P₁.append P₂).runToRound ⟨m + w, by omega⟩ stmt wit
      = (do
          let p ← liftM (P₁.runToRound ⟨m, by omega⟩ stmt wit)
          let ctx ← liftM (P₁.output p.2)
          let q ← liftM (P₂.runToRound ⟨w, by omega⟩ ctx.1 ctx.2)
          return (liftTranscriptR (pSpec₁ := pSpec₁) w hw p.1 q.1,
                  cast (Prover.prvState_add (P₁ := P₁) (P₂ := P₂) w hw hw0).symm q.2)) := by
  intro w
  induction w with
  | zero => intro _ hw0; exact absurd hw0 (lt_irrefl 0)
  | succ w ih =>
    intro hw _
    rcases Nat.eq_zero_or_pos w with rfl | hw0
    · refine Eq.trans (Prover.runToRound_mk_succ (P₁.append P₂) m (by omega) stmt wit) ?_
      rw [append_runToRound_lt stmt wit m le_rfl (by omega)]
      refine Eq.trans (append_processRound_boundary (P₁ := P₁) (P₂ := P₂) hn
        (P₁.runToRound ⟨m, by omega⟩ stmt wit)) ?_
      refine bind_congr fun p => ?_
      refine bind_congr fun ctx => ?_
      rw [runToRound_mk_one P₂ hn ctx.1 ctx.2]
      rfl
    · refine Eq.trans
        (Prover.runToRound_mk_succ (P₁.append P₂) (m + w) (by omega) stmt wit) ?_
      rw [ih (by omega) hw0]
      refine Eq.trans (processRound_bind ⟨m + w, by omega⟩ (P₁.append P₂) _ _) ?_
      refine bind_congr fun p => ?_
      refine Eq.trans (processRound_bind ⟨m + w, by omega⟩ (P₁.append P₂) _ _) ?_
      refine bind_congr fun ctx => ?_
      rw [Prover.runToRound_mk_succ P₂ w (by omega)]
      simp only [bind_pure_comp]
      exact append_processRound_add w (by omega) hw0 p.1 _


/-- `Fin.last N` written as a raw `Fin.mk`, which is the index the round inductions produce. -/
theorem runToRound_last {N : ℕ} {pSpec : ProtocolSpec N} {S W S' W' : Type}
    (P : Prover oSpec S W S' W' pSpec) (stmt : S) (wit : W) :
    P.runToRound (Fin.last N) stmt wit = P.runToRound ⟨N, by omega⟩ stmt wit := rfl

set_option maxHeartbeats 4000000 in
-- Both cases normalize a four-deep monadic bind tree through the lift lemmas.
-- Raised limit.
/--
States that running an appended prover `P₁.append P₂` with an initial statement `stmt₁` and
witness `wit₁` behaves as expected: it first runs `P₁` to obtain an intermediate statement
`stmt₂`, witness `wit₂`, and transcript `transcript₁`. Then, it runs `P₂` on `stmt₂` and `wit₂`
to produce the final statement `stmt₃`, witness `wit₃`, and transcript `transcript₂`.
The overall output is `stmt₃`, `wit₃`, and the combined transcript `transcript₁ ++ₜ transcript₂`.

The two cases are the two shapes of `Prover.append`'s `output`: when `pSpec₂` is non-empty the
handover happened at the boundary round and `output` is `P₂`'s (`append_output_pos`); when it is
empty there is no boundary round and `output` is where `P₁.output`, `P₂.input` and `P₂.output` all
fire (`append_output_zero`). Either way `P₁.output` runs exactly once, at the same point in the
sequence as on the right-hand side.
-/
theorem append_run (stmt : Stmt₁) (wit : Wit₁) :
      (P₁.append P₂).run stmt wit = (do
        let ⟨transcript₁, stmt₂, wit₂⟩ ← liftM (P₁.run stmt wit)
        let ⟨transcript₂, stmt₃, wit₃⟩ ← liftM (P₂.run stmt₂ wit₂)
        return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    unfold Prover.run
    have hrun : (P₁.append P₂).runToRound (Fin.last (m + 0)) stmt wit
        = (fun p => (liftTranscript (pSpec₂ := pSpec₂) m le_rfl (by omega) p.1,
                     cast (Prover.prvState_lt' (P₁ := P₁) (P₂ := P₂) m le_rfl (by omega)).symm p.2))
          <$> liftM (P₁.runToRound ⟨m, by omega⟩ stmt wit) :=
      append_runToRound_lt stmt wit m le_rfl (by omega)
    have hrun₂ : ∀ (s : Stmt₂) (w : Wit₂), P₂.runToRound (Fin.last 0) s w
        = pure ((default : pSpec₂.Transcript 0), P₂.input (s, w)) :=
      fun s w => Prover.runToRound_mk_zero P₂ (by omega) s w
    have hlp : ∀ (α : Type) (x : α),
        (liftM (pure x : OracleComp (oSpec + [pSpec₂.Challenge]ₒ) α) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α) = pure x := fun _ _ => rfl
    rw [hrun]
    simp only [hrun₂, runToRound_last, liftM_bind, liftM_map, map_bind, bind_map_left,
      bind_assoc, pure_bind, liftM_pure, bind_pure_comp, liftM_liftM_base,
      liftM_liftM_base_right, Functor.map_map, Function.comp]
    refine bind_congr fun a => ?_
    rw [Prover.append_output_zero (P₁ := P₁) (P₂ := P₂) rfl _
      (Prover.prvState_lt' m le_rfl (by omega)) rfl]
    have hT : liftTranscript (pSpec₂ := pSpec₂) m le_rfl (by omega) a.1
        = a.1 ++ₜ (default : pSpec₂.FullTranscript) :=
      (liftTranscriptR_zero a.1 default).symm.trans (liftTranscriptR_full a.1 default)
    simp only [liftM_bind, liftM_liftM_base, bind_assoc, cast_cast, cast_eq, bind_pure_comp,
      map_bind, Functor.map_map, Function.comp, hT]
    rfl
  · unfold Prover.run
    simp only [runToRound_last]
    rw [append_runToRound_ge (P₁ := P₁) (P₂ := P₂) stmt wit hn n le_rfl hn]
    simp only [liftM_bind, liftM_map, map_bind, bind_map_left, bind_assoc, pure_bind,
      liftM_pure, bind_pure_comp, liftM_liftM_base, liftM_liftM_base_right, Functor.map_map,
      Function.comp]
    refine Eq.trans (bind_assoc _ _ _) ?_
    refine bind_congr fun p => ?_
    refine Eq.trans (bind_assoc _ _ _) ?_
    refine bind_congr fun ctx => ?_
    refine Eq.trans (map_bind_left _ _ _) ?_
    refine bind_congr fun a => ?_
    rw [Prover.append_output_pos (P₁ := P₁) (P₂ := P₂) (Nat.pos_iff_ne_zero.mp hn)
        _ (Prover.prvState_add n le_rfl hn)]
    simp only [liftTranscriptR_full]
    exact congrArg (fun s => Prod.mk (p.1 ++ₜ a.1) <$> liftM (P₂.output s))
      (eq_of_heq ((cast_heq _ _).trans (cast_heq _ a.2)))

-- TODO: Need to define a function that "extracts" a second prover from the combined prover

end Prover

/-! ### Regression test: the appended prover's first effect

`Prover.append_run` is true only because `Prover.processRound` runs a round's `receiveChallenge`
*before* drawing that round's challenge. At the boundary round `m` the appended prover has to run
`P₁.output` inside `P₂`'s first `receiveChallenge`/`sendMessage` -- there is no other hook, and for
`m = 0` there is not even a preceding round to use -- so with the challenge drawn first the appended
prover would query the challenge oracle *before* `P₁.output`, while running `P₁` and then `P₂` runs
`P₁.output` first. `OracleComp` is a free monad (`PFunctor.FreeM`), so those are different terms,
and `append_run` would be false rather than merely hard.

The instance below witnesses that: `pSpec₁` is empty, `pSpec₂`'s single round is a challenge round,
and `P₁.output` makes one `oSpec` query. `headIsBase` reports which side of `oSpec + [Challenge]ₒ`
the computation's first query lands on. It must be `oSpec` -- swap the two binds in
`Prover.processRound` and this flips, taking `append_run` with it. -/
section OrderRegression

/-- The oracle index of a computation's first query, or `none` if it makes none. -/
private def headIdx {ι' : Type} {spec : OracleSpec ι'} {α : Type}
    (x : OracleComp spec α) : Option ι' :=
  match x with
  | .pure _ => none
  | .liftBind t _ => some t

/-- Whether a computation's first query goes to the base spec (`true`) or the challenge oracle
(`false`); `none` if it makes no query. -/
private def headIsBase {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {α : Type}
    (x : OracleComp (spec₁ + spec₂) α) : Option Bool :=
  (headIdx x).map Sum.isLeft

private abbrev tOSpec : OracleSpec Unit := fun _ => Bool

private abbrev tPSpec₁ : ProtocolSpec 0 := ProtocolSpec.empty

private abbrev tPSpec₂ : ProtocolSpec 1 := ⟨fun _ => .V_to_P, fun _ => Bool⟩

/-- A left prover whose `output` queries an oracle -- the only thing the counterexample needs. -/
private def tP₁ : Prover tOSpec Unit Unit Unit Unit tPSpec₁ where
  PrvState := fun _ => Unit
  input := fun _ => ()
  sendMessage := fun i _ => absurd i.1.isLt (by omega)
  receiveChallenge := fun i _ => absurd i.1.isLt (by omega)
  output := fun _ => do
    let _ ← (OracleSpec.query (spec := tOSpec) () : OracleComp tOSpec Bool)
    return ((), ())

/-- A trivial right prover whose single round is a challenge round. -/
private def tP₂ : Prover tOSpec Unit Unit Unit Unit tPSpec₂ where
  PrvState := fun _ => Unit
  input := fun _ => ()
  sendMessage := fun i _ => absurd i.2 (by simp)
  receiveChallenge := fun _ _ => pure (fun _ => ())
  output := fun _ => pure ((), ())

/-- The appended prover's first query is `P₁.output`'s, not the boundary challenge -- which is what
running `P₁` and then `P₂` does, and what `Prover.append_run` asserts. -/
theorem headIsBase_append_run_eq_base :
    headIsBase (Prover.run () () (tP₁.append tP₂)) = some true := rfl

end OrderRegression

end Execution
