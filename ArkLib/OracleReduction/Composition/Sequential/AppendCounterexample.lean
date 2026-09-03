/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Composition.Sequential.HandlerCommutativity

/-!
# `Reduction.append_completeness` is false as stated

`Reduction.run` runs the whole prover and *then* the whole verifier, so
`R₁.append R₂` executes **P₁, P₂, V₁, V₂**. The completeness hypotheses of the
components speak about **P₁, V₁** and **P₂, V₂**, each from a freshly sampled
`init`. Since `impl : QueryImpl oSpec (StateT σ ProbComp)` is arbitrary and
`Verifier.verify` may query `oSpec`, `V₁` in the appended run starts from the
state `P₂` left behind, and neither hypothesis applies to it.

This file makes that concrete. The oracle handler answers with a flag and then
sets it; `V₁` accepts exactly when it reads `false`; `P₂` is the only other
party that queries. Alone, each reduction is perfectly complete. Appended, `P₂`
sets the flag before `V₁` reads it, and the append rejects with probability one.

Everything is deterministic — `tInit` is `pure`, the handler only reads and
writes its flag, and neither protocol has a challenge round — so all three runs
are settled by `rfl`.

This is a *different* defect from the one `Prover.append_run` had. That was a
within-round effect ordering, repaired by reordering `Prover.processRound`.
This one is what `Reduction.append` means, and the repair is a hypothesis: the
file's own `TODO` above `append_completeness` asks for exactly this, and
statelessness of `impl` (or the commutative-monad condition it sketches) is the
answer for completeness.
-/

open OracleSpec OracleComp ProtocolSpec

namespace ArkLib.AppendCounterexample

abbrev tOSpec : OracleSpec Unit := fun _ => Bool

abbrev tPSpec : ProtocolSpec 0 := ProtocolSpec.empty

/-- Answers a query with the current flag, then sets it. -/
def tImpl : QueryImpl tOSpec (StateT Bool ProbComp) :=
  fun _ => do let s ← get; set true; return s

def tInit : ProbComp Bool := pure false

/-- A prover that makes no oracle query. -/
def tP₁ : Prover tOSpec Unit Unit Unit Unit tPSpec where
  PrvState := fun _ => Unit
  input := fun _ => ()
  sendMessage := fun i _ => absurd i.1.isLt (by omega)
  receiveChallenge := fun i _ => absurd i.1.isLt (by omega)
  output := fun _ => pure ((), ())

/-- A prover whose `output` queries once. -/
def tP₂ : Prover tOSpec Unit Unit Unit Unit tPSpec where
  PrvState := fun _ => Unit
  input := fun _ => ()
  sendMessage := fun i _ => absurd i.1.isLt (by omega)
  receiveChallenge := fun i _ => absurd i.1.isLt (by omega)
  output := fun _ => do
    let _ ← (OracleSpec.query (spec := tOSpec) () : OracleComp tOSpec Bool)
    return ((), ())

/-- Accepts exactly when the oracle answers `false`. -/
def tV₁ : Verifier tOSpec Unit Unit tPSpec where
  verify := fun _ _ => do
    let b ← (OracleSpec.query (spec := tOSpec) () : OracleComp tOSpec Bool)
    if b then failure else return ()

def tV₂ : Verifier tOSpec Unit Unit tPSpec where
  verify := fun _ _ => pure ()

instance instSampAppend :
    ∀ i : (tPSpec ++ₚ tPSpec).ChallengeIdx, SampleableType ((tPSpec ++ₚ tPSpec).Challenge i) :=
  fun i => absurd i.1.isLt (by omega)

def tR₁ : Reduction tOSpec Unit Unit Unit Unit tPSpec := ⟨tP₁, tV₁⟩
def tR₂ : Reduction tOSpec Unit Unit Unit Unit tPSpec := ⟨tP₂, tV₂⟩

/-! ## The three facts

All three computations are deterministic (`tInit` is `pure`, `tImpl` only reads
and writes its flag, and neither protocol has a challenge round), so each
simulated run reduces definitionally -- every proof below is `rfl`. -/

/-- `R₁` alone: `V₁` is the first to query, reads `false`, and accepts. -/
lemma tR₁_run :
    StateT.run' (m := ProbComp)
      (simulateQ (QueryImpl.addLift tImpl challengeQueryImpl) ((tR₁.run () ()).run)) false
      = (pure (some ((default, (), ()), ())) : ProbComp _) := rfl

/-- `R₂` alone: `P₂` queries, `V₂` accepts unconditionally. -/
lemma tR₂_run :
    StateT.run' (m := ProbComp)
      (simulateQ (QueryImpl.addLift tImpl challengeQueryImpl) ((tR₂.run () ()).run)) false
      = (pure (some ((default, (), ()), ())) : ProbComp _) := rfl

/-- The append: `P₂` queries first and sets the flag, so `V₁` reads `true` and rejects. -/
lemma tAppend_run :
    StateT.run' (m := ProbComp)
      (simulateQ (QueryImpl.addLift tImpl challengeQueryImpl)
        (((tR₁.append tR₂).run () ()).run)) false
      = (pure none : ProbComp _) := rfl

/-! ## Both components are perfectly complete; the append is not -/

lemma tComplete₁ :
    Reduction.completeness (init := tInit) (impl := tImpl)
      (Set.univ : Set (Unit × Unit)) (Set.univ : Set (Unit × Unit)) tR₁ 0 := by
  classical
  rintro ⟨⟩ ⟨⟩ _
  simp only [tInit, pure_bind]
  rw [tR₁_run]
  simp [OptionT.probFailure_eq, OptionT.run_mk]

lemma tComplete₂ :
    Reduction.completeness (init := tInit) (impl := tImpl)
      (Set.univ : Set (Unit × Unit)) (Set.univ : Set (Unit × Unit)) tR₂ 0 := by
  classical
  rintro ⟨⟩ ⟨⟩ _
  simp only [tInit, pure_bind]
  rw [tR₂_run]
  simp [OptionT.probFailure_eq, OptionT.run_mk]

lemma tNotComplete :
    ¬ Reduction.completeness (init := tInit) (impl := tImpl)
        (Set.univ : Set (Unit × Unit)) (Set.univ : Set (Unit × Unit)) (tR₁.append tR₂) 0 := by
  classical
  intro hc
  have h := hc () () (Set.mem_univ _)
  simp only [tInit, pure_bind] at h
  rw [tAppend_run] at h
  simp [OptionT.probFailure_eq, OptionT.run_mk] at h


/-- **`Reduction.append_completeness` is false as stated.** Both components are perfectly
complete for the same `init` and `impl`, and the append is not complete even at the sum of
their errors.

The hypothesis the theorem is missing is one forbidding `impl` from carrying state across
the P₂/V₁ boundary: `Reduction.run` runs the whole prover before the whole verifier, so the
appended reduction executes P₁, P₂, V₁, V₂ while the component hypotheses speak about
P₁,V₁ and P₂,V₂ from a freshly sampled `init`. Here `P₂` sets the flag that `V₁` reads. -/
theorem append_completeness_false :
    Reduction.completeness tInit tImpl
        (Set.univ : Set (Unit × Unit)) (Set.univ : Set (Unit × Unit)) tR₁ 0
      ∧ Reduction.completeness tInit tImpl
        (Set.univ : Set (Unit × Unit)) (Set.univ : Set (Unit × Unit)) tR₂ 0
      ∧ ¬ Reduction.completeness tInit tImpl
        (Set.univ : Set (Unit × Unit)) (Set.univ : Set (Unit × Unit)) (tR₁.append tR₂) (0 + 0) :=
  ⟨tComplete₁, tComplete₂, by simpa using tNotComplete⟩

/-- **The handler is not commutative**, which is what the repair hypothesis must rule out.
Asking the same query twice from `false` gives `(false, true)` in one order and
`(true, false)` in the other: this handler reports the order it was called in. -/
theorem tImpl_not_isCommutative : ¬ QueryImpl.IsCommutative tImpl := by
  intro hc
  have h := hc (OracleSpec.query (spec := tOSpec) ())
    (OracleSpec.query (spec := tOSpec) ()) false
  rw [show (simulateQ tImpl (do
        let a ← (OracleSpec.query (spec := tOSpec) () : OracleComp tOSpec Bool)
        let b ← (OracleSpec.query (spec := tOSpec) () : OracleComp tOSpec Bool)
        pure (a, b))).run false = (pure ((false, true), true) : ProbComp _) from rfl,
     show (simulateQ tImpl (do
        let b ← (OracleSpec.query (spec := tOSpec) () : OracleComp tOSpec Bool)
        let a ← (OracleSpec.query (spec := tOSpec) () : OracleComp tOSpec Bool)
        pure (a, b))).run false = (pure ((true, false), true) : ProbComp _) from rfl] at h
  simp only [evalDist_pure] at h
  have hx := congrArg (fun d => d ((false, true), true)) h
  simp at hx

end ArkLib.AppendCounterexample

