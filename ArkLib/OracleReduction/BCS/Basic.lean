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
  -- are usually presented as optimizations. Here one of them is not: it decides whether the
  security proof is reachable at all.

  Composing the per-query openings sequentially, with `ProtocolSpec.append`, gives a spec of
  `n + ∑ i, nCom i` rounds whose security proof routes through `Verifier.append_soundness` and its
  knowledge and round-by-round variants. Those are currently `sorry` in
  `ArkLib/OracleReduction/Composition/Sequential/Append.lean`: `(R₁.append R₂).run` runs both
  provers and then both verifiers, whereas running `R₁` then `R₂` interleaves them, and justifying
  the swap needs the oracle computation interpreted into a commutative monad.

  Batching the openings avoids that dependency rather than optimizing it away. If the commitment is
  homomorphic, the verifier's queries reduce to a *single* opening via a challenge-weighted
  combination, and the transformed spec is the renamed messages plus a fixed suffix -- see
  `ProtocolSpec.BCSTransform`. So the batched form is taken as the definition and the sequential
  form is derived, not the reverse.

  Batching needs the verifier's query list before the openings run, so it is stated for an
  `OracleVerifier.NonAdaptive`, whose `queryMsg` supplies exactly that list.

  ## What batching costs

  Two things, both of which must be carried explicitly rather than left in a remark:

  - a soundness term for the batching challenge;
  - an admissibility obligation on the committed data, `BCS.BatchingAdmissibility`. Homomorphy of
    the commitment *map* is not enough; see that structure's docstring.

  ## TODO

  `OracleReduction.BCSTransform`, taking an `OracleReduction` over `pSpec` to a `Reduction` over
  `pSpec.BCSTransform`, together with the completeness and soundness statements. The completeness
  statement must take a `BCS.BatchingAdmissibility` hypothesis; it is false without one for any
  norm-bounded scheme.
-/

variable {n : ℕ}

namespace ProtocolSpec

/-- Switch the type of prover's messages in a protocol specification. The directions are preserved.
-/
def renameMessage (pSpec : ProtocolSpec n) (NewMessage : pSpec.MessageIdx → Type) :
    ProtocolSpec n :=
  ⟨ pSpec.dir,
    fun i => if h : pSpec.dir i = Direction.P_to_V then NewMessage ⟨i, h⟩ else pSpec.«Type» i⟩

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
