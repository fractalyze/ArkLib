/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendCompleteness
import ArkLib.OracleReduction.Composition.Sequential.SplitProver
import ArkLib.ToVCVio.EvalDist.SoundnessBound

/-!
# Sequential composition preserves soundness

`Verifier.append_soundness` used to be stated in `Append.lean` with a `sorry`. It needs the same
two ingredients the repaired `Reduction.append_completeness` needed -- a commutative query handler,
and the second component's guarantee at every handler state -- plus one more that completeness did
not: the prover is an *arbitrary* adversary for `pSpec₁ ++ₚ pSpec₂`, so it has to be taken apart
into its two halves first. That is `Prover.takeLeft` / `Prover.dropLeft` in `SplitProver.lean`.

The argument is the union bound. Let `s₂` be the first verifier's output. Either `s₂` lands in the
intermediate language -- which is exactly `V₁`'s soundness failure, bounded by `ε₁` -- or it does
not, and then the rest of the run is `V₂`'s soundness game on a statement outside `lang₂`, bounded
by `ε₂`.
-/

open OracleComp OracleSpec ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {m n : ℕ}
  {Stmt₁ Wit₁ Stmt₂ Stmt₃ Wit₃ : Type}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

namespace Reduction

/-- The appended protocol's ambient computation monad, named so the statements below fit on a
line. -/
private abbrev Comp (oSpec : OracleSpec ι) (pSpec₁ : ProtocolSpec m) (pSpec₂ : ProtocolSpec n) :=
  OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)

/-- The adversary's private state at the cut: `takeLeft`'s output witness, and `dropLeft`'s input
witness. The soundness game quantifies over the witness types, so this is a legal choice. -/
private abbrev CutState (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂)) : Type :=
  P.PrvState (Prover.leftIdx n (Fin.last m))

/-- **An adversarial appended run, split apart.** The prover is arbitrary, so its two halves come
from `Prover.takeLeft` / `Prover.dropLeft` rather than from a `Prover.append`; past that the shape
is `append_run_run_split`'s -- the two prover halves, then `V₁`, then `V₂`, with the failure
bookkeeping as two `Option.elim`s.

`stmtOut` is the statement `takeLeft` reports; nothing downstream reads it. -/
theorem mk_append_run_run_split (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (stmtOut : Stmt₂) (stmt : Stmt₁) (wit : Wit₁) :
    (Reduction.run stmt wit (Reduction.mk P (V₁.append V₂))).run
      = (do
          let x ← (liftM ((P.takeLeft stmtOut).run stmt wit) : Comp oSpec pSpec₁ pSpec₂ _)
          let y ← (liftM ((P.dropLeft (Stmt₂ := Stmt₂)).run stmtOut
                    (cast (Prover.prvState_cut_eq P) x.2.2)) : Comp oSpec pSpec₁ pSpec₂ _)
          let o₂ ← (liftM (V₁.verify stmt x.1).run : Comp oSpec pSpec₁ pSpec₂ _)
          Option.elim o₂ (pure none) fun s₂ => do
            let o₃ ← (liftM (V₂.verify s₂ y.1).run : Comp oSpec pSpec₁ pSpec₂ _)
            Option.elim o₃ (pure none) fun s₃ =>
              pure (some ((x.1 ++ₜ y.1, y.2.1, y.2.2), s₃))) := by
  rw [run_run_flat]
  dsimp only
  rw [Prover.run_eq_takeLeft_dropLeft P stmtOut stmt wit]
  simp only [bind_assoc, pure_bind, Verifier.append, FullTranscript.append_fst,
    FullTranscript.append_snd]
  refine bind_congr fun x => bind_congr fun y => ?_
  simp only [OptionT.run_bind, Option.elimM, liftM_bind, bind_assoc]
  refine bind_congr fun o => ?_
  cases o <;> simp


section Swap

variable {σ : Type} [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]
  {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **The swap.** `Reduction.run` runs the whole prover before the whole verifier, so the
adversary's second half precedes `V₁`; the soundness hypotheses speak about `V₁` immediately
after the first half. Both read only what the first half produced and neither reads the other,
so a commutative handler cannot tell the two orders apart. -/
theorem evalDist_mk_append_run_swapped
    (hcomm : (pImplOf (pSpec₁ ++ₚ pSpec₂) impl).IsCommutative)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (stmtOut : Stmt₂) (stmt : Stmt₁) (wit : Wit₁) (s : σ) :
    𝒟[StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
        (Reduction.run stmt wit (Reduction.mk P (V₁.append V₂))).run) s]
      = 𝒟[StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl) (do
          let x ← (liftM ((P.takeLeft stmtOut).run stmt wit) : Comp oSpec pSpec₁ pSpec₂ _)
          let o₂ ← (liftM (V₁.verify stmt x.1).run : Comp oSpec pSpec₁ pSpec₂ _)
          let y ← (liftM ((P.dropLeft (Stmt₂ := Stmt₂)).run stmtOut
                    (cast (Prover.prvState_cut_eq P) x.2.2)) : Comp oSpec pSpec₁ pSpec₂ _)
          Option.elim o₂ (pure none) fun s₂ => do
            let o₃ ← (liftM (V₂.verify s₂ y.1).run : Comp oSpec pSpec₁ pSpec₂ _)
            Option.elim o₃ (pure none) fun s₃ =>
              pure (some ((x.1 ++ₜ y.1, y.2.1, y.2.2), s₃)))) s] := by
  rw [mk_append_run_run_split]
  exact hcomm.bind_prefix _ _ _ _ s

end Swap


section Phases

variable {σ : Type} [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]
  {impl : QueryImpl oSpec (StateT σ ProbComp)}
  (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
  (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
  (stmtOut : Stmt₂)

/-- **The first phase of the swapped adversarial run:** the prover's first half, then `V₁`. The
private state at the cut is kept alongside `V₁`'s output so the second phase can start from it. -/
def soundPhase₁ (stmt : Stmt₁) (wit : Wit₁) :
    Comp oSpec pSpec₁ pSpec₂ ((pSpec₁.FullTranscript × Stmt₂ × CutState P) × Option Stmt₂) := do
  let x ← (liftM ((P.takeLeft stmtOut).run stmt wit) : Comp oSpec pSpec₁ pSpec₂ _)
  let o₂ ← (liftM (V₁.verify stmt x.1).run : Comp oSpec pSpec₁ pSpec₂ _)
  pure (x, o₂)

/-- **The second phase of the swapped adversarial run:** the prover's second half, then `V₂` on
whatever `V₁` returned. -/
def soundPhase₂ (p : (pSpec₁.FullTranscript × Stmt₂ × CutState P) × Option Stmt₂) :
    Comp oSpec pSpec₁ pSpec₂
      (Option (((pSpec₁ ++ₚ pSpec₂).FullTranscript × Stmt₃ × Wit₃) × Stmt₃)) := do
  let y ← (liftM ((P.dropLeft (Stmt₂ := Stmt₂)).run stmtOut
            (cast (Prover.prvState_cut_eq P) p.1.2.2)) : Comp oSpec pSpec₁ pSpec₂ _)
  Option.elim p.2 (pure none) fun s₂ => do
    let o₃ ← (liftM (V₂.verify s₂ y.1).run : Comp oSpec pSpec₁ pSpec₂ _)
    Option.elim o₃ (pure none) fun s₃ => pure (some ((p.1.1 ++ₜ y.1, y.2.1, y.2.2), s₃))

/-- **The adversarial appended run as two phases** -- the shape `probEvent_bind_le_add`
consumes. -/
theorem evalDist_mk_append_run_phases
    (hcomm : (pImplOf (pSpec₁ ++ₚ pSpec₂) impl).IsCommutative) (stmt : Stmt₁) (wit : Wit₁)
    (s : σ) :
    𝒟[StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
        (Reduction.run stmt wit (Reduction.mk P (V₁.append V₂))).run) s]
      = 𝒟[StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
              (soundPhase₁ P V₁ stmtOut stmt wit)) s >>= fun p =>
            StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
              (soundPhase₂ P V₂ stmtOut p.1)) p.2] := by
  have hsplit : (soundPhase₁ P V₁ stmtOut stmt wit >>= soundPhase₂ P V₂ stmtOut) = (do
      let x ← (liftM ((P.takeLeft stmtOut).run stmt wit) : Comp oSpec pSpec₁ pSpec₂ _)
      let o₂ ← (liftM (V₁.verify stmt x.1).run : Comp oSpec pSpec₁ pSpec₂ _)
      let y ← (liftM ((P.dropLeft (Stmt₂ := Stmt₂)).run stmtOut
                (cast (Prover.prvState_cut_eq P) x.2.2)) : Comp oSpec pSpec₁ pSpec₂ _)
      Option.elim o₂ (pure none) fun s₂ => do
        let o₃ ← (liftM (V₂.verify s₂ y.1).run : Comp oSpec pSpec₁ pSpec₂ _)
        Option.elim o₃ (pure none) fun s₃ =>
          pure (some ((x.1 ++ₜ y.1, y.2.1, y.2.2), s₃))) := by
    simp only [soundPhase₁, soundPhase₂, bind_assoc, pure_bind]
  rw [evalDist_mk_append_run_swapped hcomm P V₁ V₂ stmtOut, ← hsplit]
  simp only [simulateQ_bind, StateT.run_bind, evalDist_bind]


variable {lang₂ : Set Stmt₂}

/-- **The first phase's bad event is `V₁`'s soundness event.** `V₁` accepted and its output
statement lies in the intermediate language -- exactly what `Verifier.soundness` bounds for `V₁`,
against the adversary's first half as the prover. -/
theorem probEvent_soundPhase₁_eq (stmt : Stmt₁) (wit : Wit₁) (s : σ) :
    Pr[ fun p : ((pSpec₁.FullTranscript × Stmt₂ × CutState P) × Option Stmt₂) × σ =>
          Option.elim p.1.2 False fun s₂ => s₂ ∈ lang₂ |
        StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
          (soundPhase₁ P V₁ stmtOut stmt wit)) s]
      = Pr[ fun r : (pSpec₁.FullTranscript × Stmt₂ × CutState P) × Stmt₂ => r.2 ∈ lang₂ |
          OptionT.mk (StateT.run' (simulateQ (pImplOf pSpec₁ impl)
            (Reduction.run stmt wit (Reduction.mk (P.takeLeft stmtOut) V₁)).run) s)] := by
  rw [OptionT.probEvent_mk, stateT_run'_eq, probEvent_map,
    probEvent_of_evalDist_eq (evalDist_simulateQ_liftM_left (impl := impl) (pSpec₂ := pSpec₂)
      (Reduction.run stmt wit (Reduction.mk (P.takeLeft stmtOut) V₁)).run s).symm,
    liftM_run_left_eq_map, simulateQ_map, StateT.run_map, probEvent_map]
  unfold soundPhase₁
  refine congrArg _ (funext fun p => ?_)
  rcases hp : p.1.2 with _ | s₂ <;> simp [hp, Function.comp]

variable {lang₃ : Set Stmt₃}

/-- **The second phase's bad event is `V₂`'s soundness event**, on the branch where `V₁` accepted
with `s₂`. The adversary's second half is run on the statement `takeLeft` reported rather than on
`s₂`, but `Prover.dropLeft_run_congr` says it never looks. -/
theorem probEvent_soundPhase₂_eq
    (x : pSpec₁.FullTranscript × Stmt₂ × CutState P) (s₂ : Stmt₂) (s₁ : σ) :
    Pr[ fun o : Option (((pSpec₁ ++ₚ pSpec₂).FullTranscript × Stmt₃ × Wit₃) × Stmt₃) =>
          Option.elim o False fun r => r.2 ∈ lang₃ |
        StateT.run' (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
          (soundPhase₂ P V₂ stmtOut (x, some s₂))) s₁]
      = Pr[ fun r : (pSpec₂.FullTranscript × Stmt₃ × Wit₃) × Stmt₃ => r.2 ∈ lang₃ |
          OptionT.mk (StateT.run' (simulateQ (pImplOf pSpec₂ impl)
            (Reduction.run s₂ (cast (Prover.prvState_cut_eq P) x.2.2)
              (Reduction.mk (P.dropLeft (Stmt₂ := Stmt₂)) V₂)).run) s₁)] := by
  have hphase : soundPhase₂ P V₂ stmtOut (x, some s₂)
      = (Option.map (fun q : (pSpec₂.FullTranscript × Stmt₃ × Wit₃) × Stmt₃ =>
            ((x.1 ++ₜ q.1.1, q.1.2.1, q.1.2.2), q.2))) <$>
          (liftM ((Reduction.run s₂ (cast (Prover.prvState_cut_eq P) x.2.2)
              (Reduction.mk (P.dropLeft (Stmt₂ := Stmt₂)) V₂)).run) :
            Comp oSpec pSpec₁ pSpec₂ _) := by
    unfold soundPhase₂
    rw [Prover.dropLeft_run_congr P stmtOut s₂, liftM_run_right_eq_map]
    simp only [Option.elim]
  rw [hphase, simulateQ_map, stateT_run'_map, probEvent_map, OptionT.probEvent_mk,
    probEvent_of_evalDist_eq (evalDist_stateT_run'_congr
      (evalDist_simulateQ_liftM_right (impl := impl) (pSpec₁ := pSpec₁)
        (Reduction.run s₂ (cast (Prover.prvState_cut_eq P) x.2.2)
          (Reduction.mk (P.dropLeft (Stmt₂ := Stmt₂)) V₂)).run s₁))]
  refine congrArg _ (funext fun o => ?_)
  cases o <;> simp [Function.comp]


/-- **With no intermediate statements the appended verifier never accepts.** `V₁` would have to
produce one, so every run fails and the soundness event has probability zero. This is the
degenerate branch of `append_soundness'`, which otherwise needs an inhabitant of `Stmt₂` to split
the adversary's prover. -/
theorem probEvent_mk_append_of_isEmpty [IsEmpty Stmt₂] (stmt : Stmt₁) (wit : Wit₁)
    {Q : ((pSpec₁ ++ₚ pSpec₂).FullTranscript × Stmt₃ × Wit₃) × Stmt₃ → Prop} (s : σ) :
    Pr[ Q | OptionT.mk (StateT.run' (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
        (Reduction.run stmt wit (Reduction.mk P (V₁.append V₂))).run) s)] = 0 := by
  have hrun : (Reduction.run stmt wit (Reduction.mk P (V₁.append V₂))).run
      = (fun _ => (none : Option (((pSpec₁ ++ₚ pSpec₂).FullTranscript × Stmt₃ × Wit₃) × Stmt₃)))
          <$> (do
            let x ← Prover.run stmt wit P
            (liftM (V₁.verify stmt x.1.fst).run : Comp oSpec pSpec₁ pSpec₂ _)) := by
    rw [run_run_flat]
    simp only [Verifier.append, OptionT.run_bind, Option.elimM, liftM_bind, bind_assoc, map_bind]
    refine bind_congr fun x => ?_
    rw [← bind_pure_comp]
    refine bind_congr fun o₂ => ?_
    cases o₂ with
    | none => simp
    | some a => exact (IsEmpty.false a).elim
  rw [hrun, simulateQ_map, stateT_run'_map, OptionT.probEvent_mk, probEvent_map]
  simp

end Phases

end Reduction

namespace Verifier

open Reduction

section Compose

variable {σ : Type} [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]
  {impl : QueryImpl oSpec (StateT σ ProbComp)} {init : ProbComp σ}
  {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}

open scoped NNReal in
/-- **Sequential composition preserves soundness.**

Two hypotheses beyond the statement that used to sit in `Append.lean`, both of them the same ones
the repaired `Reduction.append_completeness` needs:

* `hcomm` -- the handler answers queries commutatively. `Reduction.run` runs the whole prover then
  the whole verifier, so the adversary's second half precedes `V₁`, while the soundness hypotheses
  put `V₁` right after the first half.
* `h₂` at every initial state -- `V₂`'s game starts from whatever state the first phase left
  behind, not from a fresh `init`.

The adversary is an arbitrary prover for `pSpec₁ ++ₚ pSpec₂`, so it is split by
`Prover.takeLeft` / `Prover.dropLeft` before the two hypotheses can be applied. The witness types
in the soundness game are universally quantified, which is what lets the private state at the cut
serve as the first half's output witness. -/
theorem append_soundness'
    (hcomm : (pImplOf (pSpec₁ ++ₚ pSpec₂) impl).IsCommutative)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : ∀ s : σ, V₂.soundness (pure s) impl lang₂ lang₃ ε₂) :
      (V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂) := by
  intro WitIn WitOut witIn P stmtIn hstmtIn
  dsimp only
  rw [OptionT.probEvent_mk]
  rcases isEmpty_or_nonempty Stmt₂ with hE | ⟨⟨stmtOut⟩⟩
  · refine le_trans (probEvent_bind_le_of_forall_le (ε := 0) fun s₀ _ => le_of_eq ?_) (by simp)
    exact (OptionT.probEvent_mk _ _).symm.trans
      (probEvent_mk_append_of_isEmpty P V₁ V₂ stmtIn witIn s₀)
  · have hphases : ∀ s₀ : σ,
        𝒟[StateT.run' (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
            (Reduction.run stmtIn witIn (Reduction.mk P (V₁.append V₂))).run) s₀]
          = 𝒟[StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
                (soundPhase₁ P V₁ stmtOut stmtIn witIn)) s₀ >>= fun p =>
              StateT.run' (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
                (soundPhase₂ P V₂ stmtOut p.1)) p.2] := by
      intro s₀
      rw [stateT_run'_eq, evalDist_map,
        evalDist_mk_append_run_phases P V₁ V₂ stmtOut hcomm stmtIn witIn s₀]
      simp only [stateT_run'_eq, evalDist_bind, evalDist_map, map_bind]
    have hbind : 𝒟[init >>= fun s₀ =>
          StateT.run' (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
            (Reduction.run stmtIn witIn (Reduction.mk P (V₁.append V₂))).run) s₀]
        = 𝒟[(init >>= fun s₀ => StateT.run (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
              (soundPhase₁ P V₁ stmtOut stmtIn witIn)) s₀) >>= fun p =>
            StateT.run' (simulateQ (pImplOf (pSpec₁ ++ₚ pSpec₂) impl)
              (soundPhase₂ P V₂ stmtOut p.1)) p.2] := by
      simp only [evalDist_bind, bind_assoc]
      exact bind_congr fun s₀ => by rw [hphases s₀, evalDist_bind]
    rw [probEvent_of_evalDist_eq hbind, ENNReal.coe_add]
    refine le_trans (probEvent_bind_le_add
      (fun p => Option.elim p.1.2 False fun s₂ => s₂ ∈ lang₂) ?_) (add_le_add ?_ le_rfl)
    · rintro ⟨⟨x, (_ | s₂)⟩, s₁⟩ hp
      · have hnone : soundPhase₂ P V₂ stmtOut (x, none)
            = (fun _ => (none : Option (((pSpec₁ ++ₚ pSpec₂).FullTranscript × Stmt₃ × _) × Stmt₃)))
                <$> (liftM ((P.dropLeft (Stmt₂ := Stmt₂)).run stmtOut
                  (cast (Prover.prvState_cut_eq P) x.2.2)) : Comp oSpec pSpec₁ pSpec₂ _) := by
          simp only [soundPhase₂, Option.elim, ← bind_pure_comp]
        rw [hnone, simulateQ_map, stateT_run'_map, probEvent_map]
        simp
      · have hc := h₂ s₁ _ _ (cast (Prover.prvState_cut_eq P) x.2.2)
          (P.dropLeft (Stmt₂ := Stmt₂)) s₂ hp
        dsimp only at hc
        rw [pure_bind, OptionT.probEvent_mk] at hc
        rw [probEvent_soundPhase₂_eq P V₂ stmtOut x s₂ s₁, OptionT.probEvent_mk]
        exact hc
    · have hc := h₁ _ (CutState P) witIn
        (P.takeLeft stmtOut) stmtIn hstmtIn
      dsimp only at hc
      rw [OptionT.probEvent_mk] at hc
      refine le_of_eq_of_le ?_ hc
      exact probEvent_bind_congr init fun s₀ =>
        (probEvent_soundPhase₁_eq P V₁ stmtOut stmtIn witIn s₀).trans (OptionT.probEvent_mk _ _)


open scoped NNReal in
/-- **A stateless handler makes the initial state irrelevant.** Soundness from `init` then gives
soundness from every fixed state, provided `init` itself never fails: the run's distribution does
not depend on the state, so the `init`-averaged bound is the fixed-state bound scaled by `init`'s
success probability. Without `hinit` that scaling loses mass and the implication is false.

This is what discharges `append_soundness'`'s second hypothesis. -/
theorem soundness_of_isStateless {N : ℕ} {pSpec : ProtocolSpec N} {S S' : Type}
    [∀ i, SampleableType (pSpec.Challenge i)] {V : Verifier oSpec S S' pSpec}
    {langIn : Set S} {langOut : Set S'} {ε : ℝ≥0}
    (hst : impl.IsStateless) (hinit : Pr[⊥ | init] = 0)
    (h : V.soundness init impl langIn langOut ε) (s : σ) :
      V.soundness (pure s) impl langIn langOut ε := by
  intro WitIn WitOut witIn prover stmtIn hstmtIn
  have hc := h WitIn WitOut witIn prover stmtIn hstmtIn
  dsimp only at hc ⊢
  have hconst : ∀ s₀ : σ,
      StateT.run' (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
        QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
          (Reduction.run stmtIn witIn (Reduction.mk prover V)).run) s₀
        = StateT.run' (simulateQ (QueryImpl.addLift impl challengeQueryImpl :
            QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
              (Reduction.run stmtIn witIn (Reduction.mk prover V)).run) s := fun s₀ => by
    rw [QueryImpl.simulateQ_run'_of_isStateless (hst.addLift challengeQueryImpl),
      QueryImpl.simulateQ_run'_of_isStateless (hst.addLift challengeQueryImpl)]
  simp only [hconst, pure_bind] at hc ⊢
  rw [OptionT.probEvent_mk] at hc ⊢
  refine le_trans (le_of_eq ?_) hc
  rw [probEvent_bind_eq_tsum, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' hinit, one_mul]

open scoped NNReal in
/-- **Sequential composition preserves soundness, for a stateless handler.** The drop-in
replacement for the statement that used to sit in `Append.lean` with a `sorry`. A stateless
handler is trivially commutative, and `hinit` -- an initial state that is actually sampled --
is what carries `V₂`'s bound from `init` to the state the first phase leaves behind. -/
theorem append_soundness (hst : impl.IsStateless) (hinit : Pr[⊥ | init] = 0)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂) :
      (V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂) :=
  append_soundness' (hst.addLift challengeQueryImpl).isCommutative V₁ V₂ h₁
    fun s => soundness_of_isStateless hst hinit h₂ s

end Compose

end Verifier

section OracleProtocol

variable {ι : Type} {oSpec : OracleSpec ι} {m n : ℕ} {Stmt₁ Stmt₂ Stmt₃ : Type}
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)] [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {lang₁ : Set (Stmt₁ × ∀ i, OStmt₁ i)} {lang₂ : Set (Stmt₂ × ∀ i, OStmt₂ i)}
  {lang₃ : Set (Stmt₃ × ∀ i, OStmt₃ i)}

namespace OracleVerifier

open scoped NNReal in
/-- Sequential composition preserves soundness for oracle verifiers, for a stateless handler.
The oracle-side counterpart of `Verifier.append_soundness`, moved here with it. -/
theorem append_soundness (hst : impl.IsStateless) (hinit : Pr[⊥ | init] = 0)
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {ε₁ ε₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ ε₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ ε₂) :
      (V₁.append V₂).soundness init impl lang₁ lang₃ (ε₁ + ε₂) := by
  unfold soundness
  convert Verifier.append_soundness hst hinit V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

end OracleVerifier

end OracleProtocol
