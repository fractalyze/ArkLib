/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Commitments.Functional.Basic
import ArkLib.OracleReduction.Composition.Sequential.General

/-!
  # The BCS Transformation

  This file defines the (generalized) BCS transformation. This transformation was first described by
  Ben-Sasson - Chiesa - Spooner in TCC'16 for IOPs with vector queries + Merkle trees. Our
  generalized version transforms any Interactive Oracle Reduction (IOR) into an Interactive
  Reduction (IR) using commitment schemes for the respective oracle messages of the protocol. This
  captures both the original BCS transformation as well as the Polynomial IOP + Polynomial
  Commitments transform (described in Plonk, Marlin, etc.).

  More precisely, the transformation works as follows:

  1. We take in an IOR `R`.

  2. We replace every oracle statement and every prover's message with a commitment (using the
     specified corresponding commitment scheme).

  3. We look at the oracle verifier's list of queries to the prover's messages. For each query, we
     run the opening argument for the query (which is itself an interactive proof).

  After defining the transformation, our goal is to show that the transformed protocol inherits the
  security properties of its building blocks (i.e. completeness, all notions of soundness, HVZK,
  etc.)

  ## Which form is the definition

  The transform's free choices -- the order of the opening arguments, and whether they are batched
  -- are usually presented as optimizations. Here one of them is not, though for a narrower reason
  than "sequential composition is blocked".

  What is actually open, in `ArkLib/OracleReduction/Composition/Sequential/Append.lean`:

  - `Verifier.append_run` is proved, by `rfl`. The verifier side of a composition is definitional.
  - `Prover.append_run` -- running `P₁.append P₂` equals running `P₁` then `P₂` -- is `sorry`.
    `(R₁.append R₂).run` runs both provers and then both verifiers, whereas running `R₁` then `R₂`
    interleaves them, and justifying the swap wants the oracle computation in a commutative monad.
  - `Reduction.append_completeness` and the `Verifier.append_soundness` family are `sorry` in
    consequence. The n-fold statements in `Composition/Sequential/General.lean` are *derived* from
    these by induction, so they are not an independent difficulty.

  So the atom is one lemma about one append, on the prover side -- and batching does **not** escape
  it. Both routes need `Prover.append_run`. What batching buys is:

  1. A **static arity**. The sequential round count `n + ∑ i, nCom i` sums over the verifier's
     query list, a runtime value -- the stub this file replaced took `queries : List …` as a
     parameter for exactly that reason, so the transformed protocol's *type* depended on the
     execution. Batched, the arity is `n + nOpen`, known statically. That is a typing problem, not
     a proof difficulty, and it is the strongest of the three.
  2. **One application instead of an induction**: `Prover.append_run` once, at a fixed and known
     suffix where it could also be discharged by hand, rather than the `seqCompose` induction over
     a list whose length is not known until run time.
  3. A **tighter error term**: `ε + δ + η` plus one batching term, not `ε + ∑ δᵢ + ∑ ηᵢ`.

  On that basis the batched form is taken as the definition -- see `ProtocolSpec.BCSTransform` --
  and the sequential form is derived, not the reverse.

  Batching needs the verifier's query list before the openings run, so it is stated for an
  `OracleVerifier.NonAdaptive`, whose `queryMsg` supplies exactly that list.

  ## What batching costs

  Two things, both of which must be carried explicitly rather than left in a remark:

  - a soundness term for the batching challenge;
  - an admissibility obligation on the committed data, `BCS.BatchingAdmissibility`. Homomorphy of
    the commitment *map* is not enough; see that structure's docstring.

  ## What is here, and what is not

  Done, and free of `sorry`:

  - `ProtocolSpec.BCSTransform`, the batched specification, plus the structural API for
    `ProtocolSpec.renameMessage` it needs (`renameMessage_message`, `renameMessage_challenge`, and
    the index-set equalities) -- without those, nothing can be written over a renamed spec, since
    the `dite` in `renameMessage` does not reduce for a variable index.
  - `BCS.BatchingAdmissibility`, the obligation the batched route carries.
  - `Prover.commitMessages`, the **commit phase**: it runs the underlying prover, commits to each
    message, sends the commitment in its place, and retains the message and decommitment. Its
    output splits public part from private part exactly as the opening phase needs.

  Not yet here:

  - The **opening phase** prover and verifier, i.e. the batched opening argument over `pSpecOpen`,
    and the verifier side of the commit phase.
  - `OracleReduction.BCSTransform` itself, assembling the two phases with `Reduction.append`.
  - The security statements. Completeness must take a `BCS.BatchingAdmissibility` hypothesis; it is
    false without one for any norm-bounded scheme. Both it and soundness will rest on
    `Prover.append_run`, which is still `sorry` upstream of this file -- see above, and note that
    batching narrows that dependency rather than removing it.
-/

variable {n : ℕ}

namespace ProtocolSpec

/-- Switch the type of prover's messages in a protocol specification. The directions are preserved.
-/
def renameMessage (pSpec : ProtocolSpec n) (NewMessage : pSpec.MessageIdx → Type) :
    ProtocolSpec n :=
  ⟨ pSpec.dir,
    fun i => if h : pSpec.dir i = Direction.P_to_V then NewMessage ⟨i, h⟩ else pSpec.«Type» i⟩

section RenameMessage

variable (pSpec : ProtocolSpec n) (NewMessage : pSpec.MessageIdx → Type)

/-- `renameMessage` preserves directions, so it preserves the arity and the round structure. -/
@[simp]
theorem renameMessage_dir : (pSpec.renameMessage NewMessage).dir = pSpec.dir := rfl

/-- Renaming preserves the message index set definitionally: the indices are carved out by `dir`,
which `renameMessage` leaves alone. Stated so that a message index can be moved across the rename
without a transport. -/
theorem renameMessage_messageIdx :
    (pSpec.renameMessage NewMessage).MessageIdx = pSpec.MessageIdx := rfl

/-- Likewise for challenge indices. -/
theorem renameMessage_challengeIdx :
    (pSpec.renameMessage NewMessage).ChallengeIdx = pSpec.ChallengeIdx := rfl

/-- At a message index, renaming yields the new message type. This is the computation rule the
name promises, and the reason the `dite` in `renameMessage` is not observable downstream. -/
@[simp]
theorem renameMessage_message (i : pSpec.MessageIdx) :
    (pSpec.renameMessage NewMessage).Message i = NewMessage i :=
  dif_pos i.2

/-- At a challenge index, renaming changes nothing: challenges are sent by the verifier and are
not committed to. -/
@[simp]
theorem renameMessage_challenge (i : pSpec.ChallengeIdx) :
    (pSpec.renameMessage NewMessage).Challenge i = pSpec.Challenge i :=
  dif_neg (by rw [i.2]; exact fun h => Direction.noConfusion h)

end RenameMessage

/-- The **batched** BCS protocol specification: every prover message is replaced by its commitment
type, and a *single* opening argument `pSpecOpen` is appended.

The suffix is fixed -- one opening argument, not one per query -- which is why the round count is
`n + nOpen` and not `n + ∑ i, nCom i`. See the module docstring for why this, and not the per-query
form, is the definition. -/
def BCSTransform {nOpen : ℕ} (pSpec : ProtocolSpec n)
    (CommType : pSpec.MessageIdx → Type) (pSpecOpen : ProtocolSpec nOpen) :
    ProtocolSpec (n + nOpen) :=
  pSpec.renameMessage CommType ++ₚ pSpecOpen

@[simp]
theorem BCSTransform_take {nOpen : ℕ} (pSpec : ProtocolSpec n)
    (CommType : pSpec.MessageIdx → Type) (pSpecOpen : ProtocolSpec nOpen) :
    (pSpec.BCSTransform CommType pSpecOpen)⟦:n⟧ = pSpec.renameMessage CommType :=
  take_append_left'

@[simp]
theorem BCSTransform_dir {nOpen : ℕ} (pSpec : ProtocolSpec n)
    (CommType : pSpec.MessageIdx → Type) (pSpecOpen : ProtocolSpec nOpen) (i : Fin n) :
    (pSpec.BCSTransform CommType pSpecOpen).dir (Fin.castAdd nOpen i) = pSpec.dir i := by
  simp [BCSTransform, renameMessage, append]

end ProtocolSpec

namespace BCS

/-- The obligation batching imposes on a commitment scheme's *acceptance predicate*.

Reducing the verifier's `k` queries to one opening needs more than a homomorphic commitment map. If
the scheme accepts an opening only when the committed data satisfies some predicate -- Ajtai's
`ArkLib.Lattices.Ajtai.Simple.commitmentScheme` gates on `isShort`, and that gate is exactly what
its binding reduction to Module-SIS consumes -- then the combined data must satisfy that predicate
too. It need not: `isShort` is an arbitrary `Data → Bool`, closed under neither addition nor
scaling, and for a genuine norm bound `‖∑ rᵢ dᵢ‖` grows with the query count and the challenge set.

The party rejected in that case is the *honest* prover, so what fails is completeness, not
soundness. This is the trap in reading "the commitment is homomorphic, so batching is free": the
commitment *map* being linear (for Ajtai, `matVecMul_add` and `matVecMul_scalarVecMul`) says
nothing about the *scheme's* acceptance predicate.

The fix is two predicates rather than one: the per-message `isAdmissible` the scheme gates on, and
a weaker `isAdmissibleBatch` whose slack is determined by the query count `k` and the challenge
set, under which the combination is still openable. `combine_isAdmissibleBatch` is the obligation;
`isAdmissibleBatch_of_isAdmissible` records that the batched predicate is the weaker of the two, so
opening a single message is unaffected.

See `BatchingAdmissibility.ofNormBound` for the norm-bounded case, where the slack is exactly `k`
times the challenge bound. -/
structure BatchingAdmissibility (Data Challenge : Type) (k : ℕ) where
  /-- The predicate the scheme's verifier gates a single opening on. -/
  isAdmissible : Data → Prop
  /-- The weaker predicate under which a batched combination is still openable. -/
  isAdmissibleBatch : Data → Prop
  /-- The challenge-weighted combination of the `k` committed messages. -/
  combine : (Fin k → Challenge) → (Fin k → Data) → Data
  /-- The batched predicate is the weaker of the two, so batching never rejects data that a direct
  opening would have accepted. -/
  isAdmissibleBatch_of_isAdmissible : ∀ d, isAdmissible d → isAdmissibleBatch d
  /-- Combining admissible messages lands in the batched predicate. This is the hypothesis a
  norm-bounded scheme has to discharge, and the one that does not come for free from homomorphy. -/
  combine_isAdmissibleBatch : ∀ (r : Fin k → Challenge) (d : Fin k → Data),
    (∀ i, isAdmissible (d i)) → isAdmissibleBatch (combine r d)

namespace BatchingAdmissibility

variable {Data Challenge : Type} {k : ℕ}

/-- A scheme whose verifier gates on nothing batches with no obligation at all. This is the
degenerate case that "homomorphic, so batching is free" silently assumes; it is sound precisely
when the acceptance predicate is vacuous. -/
def ofNoGate (combine : (Fin k → Challenge) → (Fin k → Data) → Data) :
    BatchingAdmissibility Data Challenge k where
  isAdmissible := fun _ => True
  isAdmissibleBatch := fun _ => True
  combine := combine
  isAdmissibleBatch_of_isAdmissible := fun _ _ => trivial
  combine_isAdmissibleBatch := fun _ _ _ => trivial

/-- The norm-bounded case, which is the one that matters for lattice schemes.

Given a size function, a per-message bound `B`, a bound `c` on how far a single challenge can
scale a message, and the triangle inequality for `combine`, the batched bound is `k * (c * B)`.
The slack is exactly the query count times the challenge bound -- that product is what a lattice
scheme's parameters have to absorb, and stating it is the whole point of keeping the two predicates
apart. -/
def ofNormBound (size : Data → ℕ) (B c : ℕ) (hc : 0 < c) (hk : 0 < k)
    (combine : (Fin k → Challenge) → (Fin k → Data) → Data)
    (hcombine : ∀ (r : Fin k → Challenge) (d : Fin k → Data),
      size (combine r d) ≤ ∑ i, c * size (d i)) :
    BatchingAdmissibility Data Challenge k where
  isAdmissible := fun d => size d ≤ B
  isAdmissibleBatch := fun d => size d ≤ k * (c * B)
  combine := combine
  isAdmissibleBatch_of_isAdmissible := fun d hd =>
    hd.trans ((Nat.le_mul_of_pos_left B hc).trans (Nat.le_mul_of_pos_left (c * B) hk))
  combine_isAdmissibleBatch := fun r d hd => by
    refine (hcombine r d).trans ?_
    calc ∑ i, c * size (d i)
        ≤ ∑ _i : Fin k, c * B := Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left c (hd i)
      _ = k * (c * B) := by simp

/-- The norm-bounded slack is not vacuous: a message of size exactly `B` is admissible, and the
batched bound it certifies is `k * (c * B)`. Recorded so that a later change which collapses the
two predicates fails here rather than silently in a completeness proof. -/
theorem ofNormBound_isAdmissibleBatch_bound (size : Data → ℕ) (B c : ℕ) (hc : 0 < c) (hk : 0 < k)
    (combine : (Fin k → Challenge) → (Fin k → Data) → Data)
    (hcombine : ∀ (r : Fin k → Challenge) (d : Fin k → Data),
      size (combine r d) ≤ ∑ i, c * size (d i))
    (r : Fin k → Challenge) (d : Fin k → Data) (hd : ∀ i, size (d i) ≤ B) :
    size ((ofNormBound size B c hc hk combine hcombine).combine r d) ≤ k * (c * B) :=
  (ofNormBound size B c hc hk combine hcombine).combine_isAdmissibleBatch r d hd

end BatchingAdmissibility

end BCS

namespace Prover

open ProtocolSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type}
    {CommitmentType Decommitment : pSpec.MessageIdx → Type}

/-- What the commit phase retains for each message it has sent: the commitment (public, and the
opening phase's input statement), the message itself, and the decommitment (both private, and the
opening phase's witness). -/
abbrev Committed (pSpec : ProtocolSpec n) (CommitmentType Decommitment : pSpec.MessageIdx → Type)
    (j : pSpec.MessageIdx) : Type :=
  CommitmentType j × pSpec.Message j × Decommitment j

/-- The state of the commit-phase prover at round `k`: the underlying prover's state, together with
the committed data for every round strictly before `k`.

The bound lives in the type rather than in a separate invariant, so `output` can hand the opening
phase a *total* family with no runtime check: at `Fin.last n` every message index satisfies it. -/
def CommitState (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (CommitmentType Decommitment : pSpec.MessageIdx → Type) (k : Fin (n + 1)) : Type :=
  P.PrvState k ×
    ((j : pSpec.MessageIdx) → j.1.val < k.val → Committed pSpec CommitmentType Decommitment j)

/-- The commit phase of the BCS transform: run `P`, but commit to each message and send the
commitment in its place, retaining the message and its decommitment for the opening phase.

The resulting prover runs over `pSpec.renameMessage CommitmentType`, which has the same directions
and the same arity as `pSpec` -- only the message types change, which is what makes this a prover
for the *first* phase of `ProtocolSpec.BCSTransform` rather than a new protocol.

Its output statement carries the commitments and its output witness carries the messages and
decommitments: exactly the split a batched opening argument needs, public part to public part and
private part to private part. -/
def commitMessages (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (commit : (i : pSpec.MessageIdx) → pSpec.Message i →
      OracleComp oSpec (CommitmentType i × Decommitment i)) :
    Prover oSpec StmtIn WitIn
      (StmtOut × ((i : pSpec.MessageIdx) → CommitmentType i))
      (WitOut × ((i : pSpec.MessageIdx) → pSpec.Message i × Decommitment i))
      (pSpec.renameMessage CommitmentType) where
  PrvState := P.CommitState CommitmentType Decommitment
  input := fun x => (P.input x, fun _ h => absurd h (Nat.not_lt_zero _))
  sendMessage := fun i st => do
    let (msg, st') ← P.sendMessage i st.1
    let (cm, dc) ← commit i msg
    let extend : (j : pSpec.MessageIdx) → j.1.val < i.1.val + 1 →
        Committed pSpec CommitmentType Decommitment j := fun j hj =>
      if hlt : j.1.val < i.1.val then st.2 j hlt
      else
        have hji : j = i := Subtype.ext (Fin.ext (Nat.le_antisymm (by omega) (by omega)))
        hji ▸ (cm, msg, dc)
    return (cast (renameMessage_message pSpec CommitmentType i).symm cm, (st', extend))
  receiveChallenge := fun i st => do
    let f ← P.receiveChallenge i st.1
    return fun chal =>
      (f (cast (renameMessage_challenge pSpec CommitmentType i) chal),
        fun j hj =>
          st.2 j (by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
            · exact h
            · exfalso
              have hji : (j.1 : Fin n) = i.1 := Fin.ext h
              exact Direction.noConfusion ((hji ▸ j.2 : pSpec.dir i.1 = _).symm.trans i.2)))
  output := fun st => do
    let (stmtOut, witOut) ← P.output st.1
    let committed : (j : pSpec.MessageIdx) → Committed pSpec CommitmentType Decommitment j :=
      fun j => st.2 j (by simp only [Fin.val_last]; exact j.1.isLt)
    return ((stmtOut, fun i => (committed i).1), (witOut, fun i => (committed i).2))

/-- At the last round every message index is in range. This is the fact `commitMessages.output`
rests on to produce a *total* family of committed data with no runtime check; it is stated
separately so that a change to `CommitState`'s bound fails here rather than inside `output`. -/
theorem messageIdx_lt_last (j : pSpec.MessageIdx) : j.1.val < (Fin.last n).val := by
  simp only [Fin.val_last]; exact j.1.isLt

variable (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (commit : (i : pSpec.MessageIdx) → pSpec.Message i →
      OracleComp oSpec (CommitmentType i × Decommitment i))

/-- The commit phase does not disturb the underlying prover's initialization. -/
@[simp]
theorem commitMessages_input_fst (x : StmtIn × WitIn) :
    ((P.commitMessages commit).input x).1 = P.input x := rfl

/-- Nothing is committed before the first round. -/
theorem commitMessages_input_snd (x : StmtIn × WitIn) (j : pSpec.MessageIdx)
    (h : j.1.val < (0 : Fin (n + 1)).val) :
    ((P.commitMessages commit).input x).2 j h = absurd h (Nat.not_lt_zero _) := rfl

/-- The commit phase runs over a specification with the same directions as the original, so it is a
prover for the first `n` rounds of `ProtocolSpec.BCSTransform` and not for some other protocol. -/
theorem commitMessages_dir :
    (pSpec.renameMessage CommitmentType).dir = pSpec.dir := rfl

end Prover

namespace OracleReduction

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

variable {nOpen : ℕ} {pSpecOpen : ProtocolSpec nOpen}
    {CommitmentType : pSpec.MessageIdx → Type}

variable {StmtIn StmtOut WitIn WitOut : Type}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}

-- TODO: `BCSTransform`, sending an `OracleReduction` over `pSpec` to a `Reduction` over
-- `pSpec.BCSTransform CommitmentType pSpecOpen`. Its completeness statement must take a
-- `BCS.BatchingAdmissibility` hypothesis at the verifier's query count; see the module docstring.

end OracleReduction
