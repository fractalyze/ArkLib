/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendRbrSoundness

/-!
# Sequential composition preserves round-by-round knowledge soundness

`Verifier.append_rbrKnowledgeSoundness_of_pure` proves it, for a deterministic first verifier and a
stateless handler; the unconditional statement in `Append.lean` stays admitted, for the reason that
theorem's docstring gives.

Round-by-round knowledge soundness asks for three objects rather than one, and the two structural
ones are built here.

`Extractor.RoundByRound.appendOfPure`'s intermediate-witness family (`Extractor.WitMidAppend`) is
the first extractor's up to and including the cut and the second's past it; the cut is the first
family's *last* stage, which is exactly where the first extractor takes a `Wit₂` in, and the second
extractor's round-zero stage is a `Wit₂` by its own `eqIn`.
`Verifier.KnowledgeStateFunction.append` is the first component's knowledge state function before
the cut and the second's past it, on the statement the first verifier reported. Unlike the
language-level version in `AppendStateFunction.lean` it carries no "the first half was broken"
disjunct, and does not need one: `rbrSoundness` bounds a component's bad transitions only at
statements *outside* its input language, which is what forced the disjunct there, whereas
`rbrKnowledgeSoundness` bounds them at every statement.

The boundary round is the only interesting one, in the extractor and in the bound alike. Going from
round `m + 1` back to round `m` the extractor has to hand the first component a `Wit₂`, and the
first component's `toFun_full` will only accept one that is actually related to the statement the
first verifier reported. The second knowledge state function says such a witness exists, via its own
`toFun_next` then `toFun_empty`, so `Extractor.pickWit` selects one classically -- exactly as
`Extractor.RoundByRoundOneShot.toRoundByRoundOfRel` already does. The bound at that round is the
contrapositive of the same implication.

The probability side reuses `AppendRbrSoundness.lean` wholesale.
`Prover.probEvent_rbrKnowledgeGame_eq` drops the prover's query log, which the bad-transition event
ignores, leaving the plain game that `Prover.rbrGame_inl` and `rbrGame_inr` already split. What is
new is that the knowledge game *fixes* the witness types where the soundness game quantifies over
them, so the split-off halves need `Prover.takeLeftOut` and `Prover.dropLeftFrom` -- same rounds,
different output and input.
-/

open OracleComp OracleSpec ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ Wit₁ Wit₂ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

namespace ProtocolSpec.Transcript

/-! ### Splitting a transcript that has just been extended

The three lemmas below say what `fstUpTo`, `fstFull` and `snd` do to `Transcript.concat`, in the
three regions of an appended protocol. `AppendRbrSoundness.lean` needed the same facts, but only
inside a state function, where `StateFunction.congr_apply` could absorb them; a round-by-round
*extractor* takes a transcript as an argument, so here they have to be equations. -/

/-- Inside the first protocol, splitting off the left half commutes with extending. -/
theorem fstUpTo_concat {r : Fin (m + n)} (h₁ : (r : ℕ) + 1 ≤ m)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript r.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» r) :
    fstUpTo ((r : ℕ) + 1) h₁ (k := r.succ) (by simp) (Transcript.concat msg tr)
      = Transcript.concat
          (cast (type_append_lt (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (r : ℕ) (by omega) r.isLt)
            msg)
          (fstUpTo (r : ℕ) (by omega) (k := r.castSucc) (by simp) tr) := by
  funext i
  simp only [fstUpTo, Transcript.concat, Fin.snoc, Fin.castLT]
  by_cases hlt : (i : ℕ) < (r : ℕ)
  · rw [dif_pos hlt, dif_pos hlt]
    exact eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))
  · rw [dif_neg hlt, dif_neg hlt]
    exact eq_of_heq ((cast_heq _ _).trans
      ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _)).symm))

/-- Past the cut, extending does not change the left half. -/
theorem fstFull_concat {r : Fin (m + n)} (hmr : m ≤ (r : ℕ))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript r.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» r) :
    fstFull (k := r.succ) (by simp; omega) (Transcript.concat msg tr)
      = fstFull (k := r.castSucc) (by simp; omega) tr := by
  funext i
  have hi : (i : ℕ) < m := i.isLt
  simp only [fstFull, Transcript.concat, Fin.snoc, Fin.castLT]
  rw [dif_pos (show (i : ℕ) < (r : ℕ) by omega)]
  exact eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))

/-- Past the cut, splitting off the right half commutes with extending. The cuts are `r + 1 - m`
and `(r - m) + 1`, equal but not definitionally so, hence `HEq`. -/
theorem heq_snd_concat {r : Fin (m + n)} (hmr : m ≤ (r : ℕ))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript r.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).«Type» r) :
    HEq (Transcript.snd (k := r.succ) (Transcript.concat msg tr))
      (Transcript.concat
        (cast (type_append_ge (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (r : ℕ) hmr r.isLt) msg)
        (Transcript.snd (k := r.castSucc) tr)) := by
  refine heq_of_apply_heq (b := ⟨(r : ℕ) - m + 1, by have := r.isLt; omega⟩)
    (Fin.ext (show (r : ℕ) + 1 - m = (r : ℕ) - m + 1 by omega)) fun i hia hib => ?_
  have hib' : i < (r : ℕ) - m + 1 := hib
  simp only [Transcript.snd, Transcript.concat, Fin.snoc, Fin.castLT]
  by_cases hlt : m + i < (r : ℕ)
  · rw [dif_pos hlt, dif_pos (show i < (r : ℕ) - m by omega)]
    exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm)
  · rw [dif_neg hlt, dif_neg (show ¬ i < (r : ℕ) - m by omega)]
    exact (cast_heq _ _).trans ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _)).symm)

end ProtocolSpec.Transcript

namespace Extractor

/-- **The intermediate-witness family of a composed round-by-round extractor.** Up to and including
the cut it is the first extractor's, past the cut the second's, shifted. The cut itself is the
first family's *last* stage: that is where the first extractor takes a `Wit₂` in, and the second
extractor's round-zero stage is a `Wit₂` by its own `eqIn`. -/
def WitMidAppend (WitMid₁ : Fin (m + 1) → Type) (WitMid₂ : Fin (n + 1) → Type)
    (r : Fin (m + n + 1)) : Type :=
  have hr : (r : ℕ) < m + n + 1 := r.isLt
  if h : (r : ℕ) ≤ m then WitMid₁ ⟨r, by omega⟩ else WitMid₂ ⟨(r : ℕ) - m, by omega⟩

variable {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}

theorem witMidAppend_le {r : Fin (m + n + 1)} (h : (r : ℕ) ≤ m) :
    WitMidAppend WitMid₁ WitMid₂ r = WitMid₁ ⟨r, by omega⟩ := dif_pos h

theorem witMidAppend_gt {r : Fin (m + n + 1)} (h : ¬ (r : ℕ) ≤ m) :
    WitMidAppend WitMid₁ WitMid₂ r = WitMid₂ ⟨(r : ℕ) - m, by omega⟩ := dif_neg h

open Classical in
/-- A `Wit₂` that is valid for `s₂` whenever one exists at all, and the supplied fallback
otherwise. The choice is classical, in the same sense and for the same reason as
`Extractor.RoundByRoundOneShot.toRoundByRoundOfRel`'s: within ArkLib's extensional security
interface `extractMid` is a mathematical function, not an algorithm with a tracked running time.

It is what the boundary round of a composed extractor hands to the first component. The first
component's `toFun_full` will only accept a witness that is actually related to the statement the
first verifier reported, and at the boundary that statement is known to have one. -/
noncomputable def pickWit (rel₂ : Set (Stmt₂ × Wit₂)) (s₂ : Stmt₂) (fallback : Wit₂) : Wit₂ :=
  if h : ∃ w, (s₂, w) ∈ rel₂ then h.choose else fallback

theorem pickWit_mem {rel₂ : Set (Stmt₂ × Wit₂)} {s₂ : Stmt₂} (fallback : Wit₂)
    (h : ∃ w, (s₂, w) ∈ rel₂) : (s₂, pickWit rel₂ s₂ fallback) ∈ rel₂ := by
  rw [pickWit, dif_pos h]
  exact h.choose_spec

/-- Extending a transcript respects transport along an equality of round indices. -/
theorem heq_concat_congr {N : ℕ} {pSpec : ProtocolSpec N} {a b : Fin N} (hab : a = b)
    {T : pSpec.Transcript a.castSucc} {T' : pSpec.Transcript b.castSucc} (hT : HEq T T')
    {msg : pSpec.«Type» a} {msg' : pSpec.«Type» b} (hmsg : HEq msg msg') :
    HEq (Transcript.concat msg T) (Transcript.concat msg' T') := by
  subst hab
  rw [eq_of_heq hT, eq_of_heq hmsg]

/-- A round-by-round extractor's step respects transport along an equality of round indices. -/
theorem RoundByRound.heq_extractMid_congr {N : ℕ} {A W W' : Type} {pSpec : ProtocolSpec N}
    {WitMid : Fin (N + 1) → Type} (E : Extractor.RoundByRound oSpec A W W' pSpec WitMid)
    {a b : Fin N} (hab : a = b) (stmt : A)
    {T : pSpec.Transcript a.succ} {T' : pSpec.Transcript b.succ} (hT : HEq T T')
    {w : WitMid a.succ} {w' : WitMid b.succ} (hw : HEq w w') :
    HEq (E.extractMid a stmt T w) (E.extractMid b stmt T' w') := by
  subst hab
  rw [eq_of_heq hT, eq_of_heq hw]

/-- Transport a family of intermediate witnesses along an equality of round indices. -/
theorem witMid_index_cast {N : ℕ} {W : Fin (N + 1) → Type} {a b : Fin (N + 1)} (h : a = b) :
    W a = W b := congrArg W h

/-- Transport a partial transcript along an equality of round indices. -/
theorem transcript_index_cast {N : ℕ} {pSpec : ProtocolSpec N} {a b : Fin (N + 1)} (h : a = b) :
    pSpec.Transcript a = pSpec.Transcript b := congrArg (fun x => pSpec.Transcript x) h

/-- **The sequential composition of two round-by-round extractors**, for a deterministic first
verifier.

Before the cut it is the first extractor's. Past the cut it is the second's, on the statement the
first verifier reported. At the cut it is the second extractor's round-zero step followed by the
first's `extractOut` -- with `pickWit` in between, because `extractOut` is only useful when handed a
witness that is actually related to that statement, and at the boundary one is known to exist. -/
noncomputable def RoundByRound.appendOfPure
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (rel₂ : Set (Stmt₂ × Wit₂)) (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂) :
    Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂)
      (WitMidAppend WitMid₁ WitMid₂) where
  eqIn := (witMidAppend_le (WitMid₂ := WitMid₂) (r := 0) (by simp)).trans E₁.eqIn
  extractMid := fun r stmt tr w =>
    have hr : (r : ℕ) < m + n := r.isLt
    if h₁ : (r : ℕ) + 1 ≤ m then
      -- Both rounds lie inside the first protocol.
      cast (witMidAppend_le (WitMid₂ := WitMid₂) (r := r.castSucc) (by simpa using by omega)).symm
        (E₁.extractMid ⟨(r : ℕ), by omega⟩ stmt
          (Transcript.fstUpTo ((r : ℕ) + 1) h₁ (k := r.succ) (by simp) tr)
          (cast (witMidAppend_le (WitMid₂ := WitMid₂) (r := r.succ) (by simpa using h₁)) w))
    else if h₂ : (r : ℕ) ≤ m then
      -- The boundary round: the first protocol has just ended.
      cast (witMidAppend_le (WitMid₂ := WitMid₂) (r := r.castSucc) (by simpa using h₂)).symm
        (cast (witMid_index_cast (W := WitMid₁) (Fin.ext (show m = (r : ℕ) by omega)))
          (E₁.extractOut stmt (Transcript.fstFull (k := r.succ) (by simp; omega) tr)
            (pickWit rel₂ (verify stmt (Transcript.fstFull (k := r.succ) (by simp; omega) tr))
              (cast E₂.eqIn (E₂.extractMid ⟨0, by omega⟩
                (verify stmt (Transcript.fstFull (k := r.succ) (by simp; omega) tr))
                (cast (transcript_index_cast (pSpec := pSpec₂)
                  (Fin.ext (show ((r : ℕ) + 1) - m = 1 by omega)))
                  (Transcript.snd (k := r.succ) tr))
                (cast (witMid_index_cast (W := WitMid₂)
                  (Fin.ext (show ((r : ℕ) + 1) - m = 1 by omega)))
                  (cast (witMidAppend_gt (WitMid₁ := WitMid₁) (r := r.succ)
                    (by simp; omega)) w)))))))
    else
      -- Strictly inside the second protocol.
      cast (witMidAppend_gt (WitMid₁ := WitMid₁) (r := r.castSucc)
          (by simpa using by omega)).symm
        (E₂.extractMid ⟨(r : ℕ) - m, by omega⟩
          (verify stmt (Transcript.fstFull (k := r.succ) (by simp; omega) tr))
          (cast (transcript_index_cast (pSpec := pSpec₂)
            (Fin.ext (show ((r : ℕ) + 1) - m = ((r : ℕ) - m) + 1 by omega)))
            (Transcript.snd (k := r.succ) tr))
          (cast (witMid_index_cast (W := WitMid₂)
            (Fin.ext (show ((r : ℕ) + 1) - m = ((r : ℕ) - m) + 1 by omega)))
            (cast (witMidAppend_gt (WitMid₁ := WitMid₁) (r := r.succ) (by simp; omega)) w)))
  extractOut := fun stmt tr wit₃ =>
    if h : m + n ≤ m then
      -- The second protocol has no rounds at all.
      cast (witMidAppend_le (WitMid₂ := WitMid₂) (r := Fin.last (m + n)) (by simpa using h)).symm
        (cast (witMid_index_cast (W := WitMid₁) (Fin.ext (show m = m + n by omega)))
          (E₁.extractOut stmt tr.fst
            (pickWit rel₂ (verify stmt tr.fst)
              (cast E₂.eqIn (cast (witMid_index_cast (W := WitMid₂)
                  (Fin.ext (show (n : ℕ) = 0 by omega)))
                (E₂.extractOut (verify stmt tr.fst) tr.snd wit₃))))))
    else
      cast (witMidAppend_gt (WitMid₁ := WitMid₁) (r := Fin.last (m + n))
          (by simpa using h)).symm
        (cast (witMid_index_cast (W := WitMid₂)
            (Fin.ext (show (n : ℕ) = m + n - m by omega)))
          (E₂.extractOut (verify stmt tr.fst) tr.snd wit₃))

end Extractor

namespace Verifier.KnowledgeStateFunction

open Extractor

section Congr

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- A knowledge state function does not distinguish transcripts and intermediate witnesses that
agree, even when their round indices are only propositionally equal. -/
theorem congr_heq {N : ℕ} {A B W W' : Type} {pSpec : ProtocolSpec N}
    {V : Verifier oSpec A B pSpec} {relIn : Set (A × W)} {relOut : Set (B × W')}
    {WitMid : Fin (N + 1) → Type} {E : Extractor.RoundByRound oSpec A W W' pSpec WitMid}
    (kSF : V.KnowledgeStateFunction init impl relIn relOut E)
    {a b : Fin (N + 1)} (hab : a = b) (stmt : A)
    {T : pSpec.Transcript a} {T' : pSpec.Transcript b} (hT : HEq T T')
    {w : WitMid a} {w' : WitMid b} (hw : HEq w w') :
    (kSF a stmt T w ↔ kSF b stmt T' w') := by
  subst hab
  rw [eq_of_heq hT, eq_of_heq hw]

/-- **A deterministic verifier's verdict is reachable.** If the verdict is related to the witness in
hand then the event has positive probability, which is the form `KnowledgeStateFunction.toFun_full`
asks for. The knowledge counterpart of `StateFunction.not_mem_of_pure`. -/
theorem probEvent_pos_of_pure {A B W : Type} {N : ℕ} {pSpec : ProtocolSpec N}
    {V : Verifier oSpec A B pSpec} {rel : Set (B × W)}
    (verify : A → pSpec.FullTranscript → B) (hV : V = ⟨fun s t => pure (verify s t)⟩)
    (hinit : (support init).Nonempty) (stmt : A) (tr : pSpec.FullTranscript) (wit : W)
    (h : (verify stmt tr, wit) ∈ rel) :
    0 < Pr[fun stmtOut => (stmtOut, wit) ∈ rel |
      OptionT.mk do (simulateQ impl (V.run stmt tr)).run' (← init)] := by
  rw [pos_iff_ne_zero]
  intro hzero
  subst hV
  simp only [Verifier.run, StateT.run'_eq, OptionT.mk_bind, probEvent_eq_zero_iff, support_bind,
    OptionT.support_liftM, Set.mem_iUnion, OptionT.mem_support_iff, OptionT.run_mk, support_map,
    Set.mem_image, Prod.exists, exists_and_right, exists_eq_right, exists_prop,
    forall_exists_index, and_imp] at hzero
  obtain ⟨s, hs⟩ := hinit
  have heq :
      ((simulateQ impl (pure (verify stmt tr) : OptionT (OracleComp oSpec) B)).run s :
        ProbComp (Option B × σ)) = pure (some (verify stmt tr), s) := rfl
  exact hzero _ s hs s (by rw [heq]; simp) h

end Congr

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
  {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}

/-- **The sequential composition of two knowledge state functions**, for a deterministic first
verifier: the first component's before the cut, the second component's past it, on the statement
the first verifier reported. -/
noncomputable def append
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hinit : (support init).Nonempty) :
    (V₁.append V₂).KnowledgeStateFunction init impl rel₁ rel₃
      (Extractor.RoundByRound.appendOfPure E₁ E₂ rel₂ verify) where
  toFun := fun r stmt tr w =>
    if h : (r : ℕ) ≤ m then
      kSF₁ ⟨r, by have := r.isLt; omega⟩ stmt (Transcript.fstUpTo (r : ℕ) h le_rfl tr)
        (cast (Extractor.witMidAppend_le h) w)
    else
      kSF₂ ⟨(r : ℕ) - m, by have := r.isLt; omega⟩
        (verify stmt (Transcript.fstFull (by omega) tr))
        (Transcript.snd tr) (cast (Extractor.witMidAppend_gt h) w)
  toFun_empty := by
    intro stmt w
    rw [dif_pos (show ((0 : Fin (m + n + 1)) : ℕ) ≤ m by simp)]
    rw [← cast_cast (ha := Extractor.witMidAppend_le (WitMid₁ := WitMid₁) (WitMid₂ := WitMid₂)
      (r := 0) (by simp))]
    refine (kSF₁.toFun_empty stmt _).trans (congr_heq kSF₁ (a := 0) rfl stmt ?_ HEq.rfl)
    exact Transcript.heq_of_apply_heq rfl fun i hia _ => absurd hia (Nat.not_lt_zero i)
  toFun_next := by
    intro r hDir stmt tr msg w h
    have hr : (r : ℕ) < m + n := r.isLt
    have hsucc : ((r.succ : Fin (m + n + 1)) : ℕ) = (r : ℕ) + 1 := rfl
    have hcast : ((r.castSucc : Fin (m + n + 1)) : ℕ) = (r : ℕ) := rfl
    by_cases h₁ : (r : ℕ) + 1 ≤ m
    · -- Both rounds lie inside the first protocol.
      have hdir₁ : pSpec₁.dir ⟨(r : ℕ), by omega⟩ = .P_to_V := by
        rw [← dir_append_lt (pSpec₂ := pSpec₂) (r : ℕ) (by omega) r.isLt]; exact hDir
      rw [dif_pos (show ((r.succ : Fin (m + n + 1)) : ℕ) ≤ m by omega)] at h
      replace h : kSF₁ ⟨(r : ℕ) + 1, by omega⟩ stmt
          (Transcript.fstUpTo ((r : ℕ) + 1) h₁ (k := r.succ) (by simp) (Transcript.concat msg tr))
          (cast (Extractor.witMidAppend_le
            (show ((r.succ : Fin (m + n + 1)) : ℕ) ≤ m by omega)) w) := h
      rw [Transcript.fstUpTo_concat] at h
      rw [dif_pos (show ((r.castSucc : Fin (m + n + 1)) : ℕ) ≤ m by omega)]
      simp only [Extractor.RoundByRound.appendOfPure, dif_pos h₁, cast_cast, cast_eq]
      rw [Transcript.fstUpTo_concat]
      exact kSF₁.toFun_next ⟨(r : ℕ), by omega⟩ hdir₁ stmt _ _ _ h
    · by_cases h₂ : (r : ℕ) ≤ m
      · -- The boundary round: the first protocol has just ended.
        have hrm : (r : ℕ) = m := by omega
        have hn : 0 < n := by omega
        have hdir₂ : pSpec₂.dir ⟨0, hn⟩ = .P_to_V := by
          rw [← dir_append_add (pSpec₁ := pSpec₁) 0 hn (by omega),
            show (⟨m + 0, by omega⟩ : Fin (m + n)) = r from Fin.ext (by simp [hrm])]
          exact hDir
        rw [dif_neg (show ¬ ((r.succ : Fin (m + n + 1)) : ℕ) ≤ m by omega),
          Transcript.fstFull_concat (by omega)] at h
        rw [dif_pos (show ((r.castSucc : Fin (m + n + 1)) : ℕ) ≤ m by omega)]
        simp only [Extractor.RoundByRound.appendOfPure, dif_neg h₁, dif_pos h₂,
          Transcript.fstFull_concat (by omega : m ≤ (r : ℕ)), cast_cast]
        -- The statement the first verifier reported has a witness: either the second knowledge
        -- state function says so at its round zero, or the disjunct did.
        have hex : ∃ v, (verify stmt (Transcript.fstFull (by omega) tr), v) ∈ rel₂ := by
          · have hkSF₂ : kSF₂ (⟨0, hn⟩ : Fin n).succ
                (verify stmt (Transcript.fstFull (by omega) tr))
                (cast (Extractor.transcript_index_cast (pSpec := pSpec₂)
                  (b := (⟨0, hn⟩ : Fin n).succ)
                  (Fin.ext (show ((r : ℕ) + 1) - m = 0 + 1 by omega)))
                  (Transcript.snd (k := r.succ) (Transcript.concat msg tr)))
                (cast (Extractor.witMid_index_cast (W := WitMid₂)
                  (b := (⟨0, hn⟩ : Fin n).succ)
                  (Fin.ext (show ((r : ℕ) + 1) - m = 0 + 1 by omega)))
                  (cast (Extractor.witMidAppend_gt (WitMid₁ := WitMid₁) (r := r.succ)
                    (by omega)) w)) :=
              (congr_heq kSF₂ (Fin.ext (show ((r : ℕ) + 1) - m = 0 + 1 by omega)) _
                (cast_heq _ _).symm (cast_heq _ _).symm).mp h
            set T₂ := cast (Extractor.transcript_index_cast (pSpec := pSpec₂)
              (b := (⟨0, hn⟩ : Fin n).succ)
              (Fin.ext (show ((r : ℕ) + 1) - m = 0 + 1 by omega)))
              (Transcript.snd (k := r.succ) (Transcript.concat msg tr)) with hT₂
            have hconcat : Transcript.concat (T₂ (Fin.last 0))
                (fun i => Fin.elim0 i : pSpec₂.Transcript (⟨0, hn⟩ : Fin n).castSucc) = T₂ := by
              funext i
              refine Fin.lastCases ?_ (fun j => Fin.elim0 j) i
              exact Fin.snoc_last _ _
            have key := kSF₂.toFun_next ⟨0, hn⟩ hdir₂ _ _ _ _ (hconcat.symm ▸ hkSF₂)
            exact ⟨_, (kSF₂.toFun_empty _ _).mpr ((congr_heq kSF₂ (b := 0) rfl _
              (Transcript.heq_of_apply_heq rfl fun i hia _ => absurd hia (Nat.not_lt_zero i))
              HEq.rfl).mp key)⟩
        refine (congr_heq kSF₁ (Fin.ext (show m = (r : ℕ) by omega)) stmt ?_
          ((cast_heq _ _).symm)).mp
          (kSF₁.toFun_full stmt (Transcript.fstFull (by omega) tr) _
            (probEvent_pos_of_pure verify hVerify hinit stmt _ _
              (Extractor.pickWit_mem _ hex)))
        refine Transcript.heq_of_apply_heq (Fin.ext (show m = (r : ℕ) by omega))
          fun i hia hib => ?_
        have hia' : i < m := hia
        exact (Transcript.fstFull_apply_heq _ tr i hia' (by omega)).trans
          (Transcript.fstUpTo_apply_heq _ _ _ tr i hib (by omega)).symm
      · -- Strictly inside the second protocol.
        have hmr : m < (r : ℕ) := by omega
        have hdir₂ : pSpec₂.dir ⟨(r : ℕ) - m, by omega⟩ = .P_to_V := by
          rw [← dir_append_ge (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (r : ℕ) (by omega) r.isLt]
          exact hDir
        rw [dif_neg (show ¬ ((r.succ : Fin (m + n + 1)) : ℕ) ≤ m by omega),
          Transcript.fstFull_concat (by omega)] at h
        rw [dif_neg (show ¬ ((r.castSucc : Fin (m + n + 1)) : ℕ) ≤ m by omega)]
        simp only [Extractor.RoundByRound.appendOfPure, dif_neg h₁, dif_neg h₂,
          Transcript.fstFull_concat (by omega : m ≤ (r : ℕ)), cast_cast, cast_eq]
        have htr : (cast (Extractor.transcript_index_cast (pSpec := pSpec₂)
              (Fin.ext (show ((r : ℕ) + 1) - m = ((r : ℕ) - m) + 1 by omega)))
              (Transcript.snd (k := r.succ) (Transcript.concat msg tr)))
            = Transcript.concat
                (cast (type_append_ge (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (r : ℕ)
                  (by omega) r.isLt) msg)
                (Transcript.snd (k := r.castSucc) tr) :=
          eq_of_heq ((cast_heq _ _).trans (Transcript.heq_snd_concat (by omega) tr msg))
        rw [htr]
        refine kSF₂.toFun_next ⟨(r : ℕ) - m, by omega⟩ hdir₂ _ _ _ _ ?_
        exact (congr_heq kSF₂
          (Fin.ext (show ((r : ℕ) + 1) - m = ((r : ℕ) - m) + 1 by omega)) _
          (Transcript.heq_snd_concat (by omega) tr msg)
          ((cast_heq _ _).trans (cast_heq _ _).symm)).mp h
  toFun_full := by
    intro stmt (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) witOut hpos
    have hrun : ((V₁.append V₂).run stmt tr) = V₂.run (verify stmt tr.fst) tr.snd := by
      subst hVerify; simp [Verifier.append, Verifier.run]
    rw [hrun] at hpos
    have hfull₂ := kSF₂.toFun_full (verify stmt tr.fst) tr.snd witOut hpos
    by_cases h : m + n ≤ m
    · -- The second protocol has no rounds at all.
      rw [dif_pos (show ((Fin.last (m + n) : Fin (m + n + 1)) : ℕ) ≤ m by simpa using h)]
      simp only [Extractor.RoundByRound.appendOfPure, dif_pos h, cast_cast]
      have hex : ∃ v, (verify stmt tr.fst, v) ∈ rel₂ := by
        refine ⟨cast E₂.eqIn (cast (Extractor.witMid_index_cast (W := WitMid₂)
          (a := Fin.last n) (b := 0) (Fin.ext (show (n : ℕ) = 0 by omega)))
          (E₂.extractOut (verify stmt tr.fst) tr.snd witOut)), ?_⟩
        refine (kSF₂.toFun_empty _ _).mpr ?_
        exact (congr_heq kSF₂ (b := 0) (Fin.ext (show (n : ℕ) = 0 by omega)) _
          (Transcript.heq_of_apply_heq (Fin.ext (show (n : ℕ) = 0 by omega))
            fun i hia _ => absurd (hia : i < n) (by omega))
          (cast_heq _ _).symm).mp hfull₂
      rw [← Transcript.fstFull_last tr]
      have hT : HEq (Transcript.fstFull (k := Fin.last (m + n)) (Nat.le_add_right m n) tr)
          (Transcript.fstUpTo ((Fin.last (m + n) : Fin (m + n + 1)) : ℕ) h
            (k := Fin.last (m + n)) le_rfl tr) := by
        have hpt : ∀ (i : ℕ) (hia : i < m) (hib : i < m + n),
            HEq (Transcript.fstFull (k := Fin.last (m + n)) (Nat.le_add_right m n) tr ⟨i, hia⟩)
              (Transcript.fstUpTo ((Fin.last (m + n) : Fin (m + n + 1)) : ℕ) h
                (k := Fin.last (m + n)) le_rfl tr ⟨i, hib⟩) := by
          intro i hia hib
          refine HEq.trans (Transcript.fstFull_apply_heq (k := Fin.last (m + n))
            (Nat.le_add_right m n) tr i hia hib) ?_
          exact (Transcript.fstUpTo_apply_heq ((Fin.last (m + n) : Fin (m + n + 1)) : ℕ) h
            (k := Fin.last (m + n)) le_rfl tr i hib hib).symm
        exact Transcript.heq_of_apply_heq (a := Fin.last m)
          (b := (⟨m + n, by omega⟩ : Fin (m + 1)))
          (Fin.ext (show m = m + n by omega)) hpt
      exact (congr_heq kSF₁ (Fin.ext (show m = m + n by omega)) stmt hT
        (cast_heq _ _).symm).mp
        (kSF₁.toFun_full stmt _ _
          (probEvent_pos_of_pure verify hVerify hinit stmt _ _
            (Extractor.pickWit_mem _ (Transcript.fstFull_last tr ▸ hex))))
    · rw [dif_neg (show ¬ ((Fin.last (m + n) : Fin (m + n + 1)) : ℕ) ≤ m by simpa using h)]
      simp only [Extractor.RoundByRound.appendOfPure, dif_neg h, cast_cast]
      rw [Transcript.fstFull_last tr]
      exact (congr_heq kSF₂ (Fin.ext (show (n : ℕ) = m + n - m by omega)) _
        (Transcript.heq_snd_last tr).symm (cast_heq _ _).symm).mp hfull₂

end Verifier.KnowledgeStateFunction

namespace Verifier.KnowledgeStateFunction

section Readoff

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
  {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
  {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
  {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
  {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
  {kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁}
  {kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂}
  {verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂}
  {hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩} {hsupp : (support init).Nonempty}

/-- An existential over intermediate witnesses transports along the equality of witness types. -/
theorem exists_cast_iff {α β : Type} (h : α = β) {p : α → Prop} {q : β → Prop}
    (hpq : ∀ a, p a ↔ q (cast h a)) : (∃ a, p a) ↔ (∃ b, q b) := by
  subst h
  exact exists_congr hpq

/-- Before the cut the composed knowledge state function is the first component's, read off the
lifted transcript. -/
theorem append_toFun_liftTranscript (stmt : Stmt₁) (v : ℕ) (hv : v ≤ m)
    (T : pSpec₁.Transcript ⟨v, by omega⟩)
    (w : Extractor.WitMidAppend WitMid₁ WitMid₂ ⟨v, by omega⟩) :
    (append init impl V₁ V₂ E₁ E₂ kSF₁ kSF₂ verify hVerify hsupp).toFun ⟨v, by omega⟩ stmt
        (liftTranscript (pSpec₂ := pSpec₂) v hv (by omega) T) w
      ↔ kSF₁ ⟨v, by omega⟩ stmt T
          (cast (Extractor.witMidAppend_le (r := (⟨v, by omega⟩ : Fin (m + n + 1))) hv) w) := by
  show dite _ _ _ ↔ _
  rw [dif_pos (show ((⟨v, by omega⟩ : Fin (m + n + 1)) : ℕ) ≤ m from hv),
    Transcript.fstUpTo_liftTranscript v hv (by omega) T]

/-- Before the cut the composed extractor is the first component's, on the lifted transcript. -/
theorem append_extractMid_lt (stmt : Stmt₁) (v : ℕ) (hv : v + 1 ≤ m) (hvn : v < m + n)
    (T : pSpec₁.Transcript ⟨v + 1, by omega⟩)
    (w : Extractor.WitMidAppend WitMid₁ WitMid₂ ⟨v + 1, by omega⟩) :
    cast (Extractor.witMidAppend_le (WitMid₂ := WitMid₂)
        (r := (⟨v, by omega⟩ : Fin (m + n + 1))) (show v ≤ m by omega))
        ((Extractor.RoundByRound.appendOfPure E₁ E₂ rel₂ verify).extractMid ⟨v, hvn⟩ stmt
          (liftTranscript (pSpec₂ := pSpec₂) (v + 1) hv (by omega) T) w)
      = E₁.extractMid ⟨v, by omega⟩ stmt T
          (cast (Extractor.witMidAppend_le (WitMid₂ := WitMid₂)
            (r := (⟨v + 1, by omega⟩ : Fin (m + n + 1))) (show v + 1 ≤ m from hv)) w) := by
  simp only [Extractor.RoundByRound.appendOfPure, dif_pos hv, cast_cast]
  have hfst : Transcript.fstUpTo (v + 1) hv (k := (⟨v, hvn⟩ : Fin (m + n)).succ) (by simp)
      (liftTranscript (pSpec₂ := pSpec₂) (v + 1) hv (by omega) T) = T :=
    Transcript.fstUpTo_liftTranscript (v + 1) hv (by omega) T
  rw [hfst]
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

/-- Past the cut the composed knowledge state function is the second component's, on the statement
the first verifier reported. -/
theorem append_toFun_liftTranscriptR (stmt : Stmt₁) (w : ℕ) (hw : w ≤ n) (hw₀ : 0 < w)
    (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.Transcript ⟨w, by omega⟩)
    (x : Extractor.WitMidAppend WitMid₁ WitMid₂ ⟨m + w, by omega⟩) :
    (append init impl V₁ V₂ E₁ E₂ kSF₁ kSF₂ verify hVerify hsupp).toFun ⟨m + w, by omega⟩ stmt
        (liftTranscriptR (pSpec₁ := pSpec₁) w hw T₁ T₂) x
      ↔ kSF₂ ⟨w, by omega⟩ (verify stmt T₁) T₂
          (cast (Extractor.witMid_index_cast (W := WitMid₂)
              (Fin.ext (show m + w - m = w by omega)))
            (cast (Extractor.witMidAppend_gt (WitMid₁ := WitMid₁)
              (r := (⟨m + w, by omega⟩ : Fin (m + n + 1)))
              (show ¬ m + w ≤ m by omega)) x)) := by
  show dite _ _ _ ↔ _
  rw [dif_neg (show ¬ m + w ≤ m by omega), Transcript.fstFull_liftTranscriptR w hw T₁ T₂]
  exact congr_heq kSF₂ (Fin.ext (show m + w - m = w by omega)) _
    (Transcript.heq_snd_liftTranscriptR w hw T₁ T₂) (cast_heq _ _).symm

/-- At the cut the composed knowledge state function is still the first component's. -/
theorem append_toFun_liftTranscriptR_zero (stmt : Stmt₁)
    (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.Transcript ⟨0, by omega⟩)
    (x : Extractor.WitMidAppend WitMid₁ WitMid₂ ⟨m + 0, by omega⟩) :
    (append init impl V₁ V₂ E₁ E₂ kSF₁ kSF₂ verify hVerify hsupp).toFun ⟨m + 0, by omega⟩ stmt
        (liftTranscriptR (pSpec₁ := pSpec₁) 0 (by omega) T₁ T₂) x
      ↔ kSF₁ (Fin.last m) stmt T₁
          (cast (Extractor.witMidAppend_le (WitMid₂ := WitMid₂)
            (r := (⟨m + 0, by omega⟩ : Fin (m + n + 1))) (show m + 0 ≤ m by omega)) x) := by
  show dite _ _ _ ↔ _
  rw [dif_pos (show m + 0 ≤ m from le_rfl)]
  refine congr_heq kSF₁ rfl stmt ?_ ((cast_heq _ _).trans (cast_heq _ _).symm)
  refine Transcript.heq_of_apply_heq rfl fun i hia hib => ?_
  have hi : i < m := hib
  simp only [Transcript.fstUpTo, liftTranscriptR, dif_pos hi]
  exact (cast_heq _ _).trans (cast_heq _ _)

/-- Strictly past the cut the composed extractor is the second component's. -/
theorem heq_append_extractMid_gt (stmt : Stmt₁) (w : ℕ) (hw : w < n) (hw₀ : 0 < w)
    (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.Transcript ⟨w, by omega⟩)
    (msg : pSpec₂.«Type» ⟨w, hw⟩)
    (x : Extractor.WitMidAppend WitMid₁ WitMid₂ ⟨m + w + 1, by omega⟩) :
    HEq ((Extractor.RoundByRound.appendOfPure E₁ E₂ rel₂ verify).extractMid
          (⟨m + w, by omega⟩ : Fin (m + n)) stmt
          (Transcript.concat
            (cast (type_append_add (pSpec₁ := pSpec₁) w hw (by omega)).symm msg)
            (liftTranscriptR (pSpec₁ := pSpec₁) w hw.le T₁ T₂)) x)
        (E₂.extractMid ⟨w, hw⟩ (verify stmt T₁) (Transcript.concat msg T₂)
          (cast (Extractor.witMid_index_cast (W := WitMid₂)
              (Fin.ext (show m + w + 1 - m = w + 1 by omega)))
            (cast (Extractor.witMidAppend_gt (WitMid₁ := WitMid₁)
              (r := (⟨m + w + 1, by omega⟩ : Fin (m + n + 1)))
              (show ¬ m + w + 1 ≤ m by omega)) x))) := by
  have hfst : Transcript.fstFull (k := (⟨m + w, by omega⟩ : Fin (m + n)).succ)
      (show m ≤ m + w + 1 by omega)
      (Transcript.concat (cast (type_append_add (pSpec₁ := pSpec₁) w hw (by omega)).symm msg)
        (liftTranscriptR (pSpec₁ := pSpec₁) w hw.le T₁ T₂)) = T₁ := by
    rw [Transcript.fstFull_concat (show m ≤ m + w by omega)]
    exact Transcript.fstFull_liftTranscriptR w hw.le T₁ T₂
  simp only [Extractor.RoundByRound.appendOfPure,
    dif_neg (show ¬ m + w + 1 ≤ m by omega), dif_neg (show ¬ m + w ≤ m by omega), hfst]
  refine HEq.trans (cast_heq _ _) ?_
  refine Extractor.RoundByRound.heq_extractMid_congr E₂
    (Fin.ext (show m + w - m = w by omega)) _ ?_ ?_
  · refine HEq.trans (cast_heq _ _) ?_
    refine HEq.trans (Transcript.heq_snd_concat (show m ≤ m + w by omega) _ _) ?_
    exact Extractor.heq_concat_congr (Fin.ext (show m + w - m = w by omega))
      (Transcript.heq_snd_liftTranscriptR w hw.le T₁ T₂)
      ((cast_heq _ _).trans (cast_heq _ _))
  · exact ((cast_heq _ _).trans (cast_heq _ _)).trans
      ((cast_heq _ _).trans (cast_heq _ _)).symm

/-- At the cut the composed extractor ends in the first component's `extractOut`, on some witness
`pickWit` selected. Which one it selected does not matter downstream -- `pickWit` is valid for
*every* fallback once the statement has a witness at all -- so the fallback stays existential. -/
theorem heq_append_extractMid_boundary (stmt : Stmt₁) (hn : 0 < n)
    (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.Transcript ⟨0, by omega⟩)
    (msg : pSpec₂.«Type» ⟨0, hn⟩)
    (x : Extractor.WitMidAppend WitMid₁ WitMid₂ ⟨m + 0 + 1, by omega⟩) :
    ∃ fb : Wit₂, HEq ((Extractor.RoundByRound.appendOfPure E₁ E₂ rel₂ verify).extractMid
          (⟨m + 0, by omega⟩ : Fin (m + n)) stmt
          (Transcript.concat
            (cast (type_append_add (pSpec₁ := pSpec₁) 0 hn (by omega)).symm msg)
            (liftTranscriptR (pSpec₁ := pSpec₁) 0 (by omega) T₁ T₂)) x)
        (E₁.extractOut stmt T₁ (Extractor.pickWit rel₂ (verify stmt T₁) fb)) := by
  have hfst : Transcript.fstFull (k := (⟨m + 0, by omega⟩ : Fin (m + n)).succ)
      (show m ≤ m + 0 + 1 by omega)
      (Transcript.concat (cast (type_append_add (pSpec₁ := pSpec₁) 0 hn (by omega)).symm msg)
        (liftTranscriptR (pSpec₁ := pSpec₁) 0 (by omega) T₁ T₂)) = T₁ := by
    rw [Transcript.fstFull_concat (show m ≤ m + 0 by omega)]
    exact Transcript.fstFull_liftTranscriptR 0 (by omega) T₁ T₂
  exact ⟨_, by
    simp only [Extractor.RoundByRound.appendOfPure,
      dif_neg (show ¬ m + 0 + 1 ≤ m by omega), dif_pos (show m + 0 ≤ m by omega), hfst]
    exact (cast_heq _ _).trans (cast_heq _ _)⟩

/-- **The bad-transition event at a left-half challenge round is the first component's.** Every
piece transports: the transcript by `fstUpTo_liftTranscript`, the intermediate witness by the
equality of witness types, and the extracted witness by `append_extractMid_lt`. -/
theorem event_inl (stmt : Stmt₁) (i₁ : pSpec₁.ChallengeIdx)
    (T₁ : pSpec₁.Transcript ⟨(i₁.1 : ℕ), by omega⟩) (c₁ : pSpec₁.«Type» i₁.1) :
    (∃ witMid : Extractor.WitMidAppend WitMid₁ WitMid₂
          ⟨(i₁.1 : ℕ) + 1, Nat.succ_lt_succ (lt_of_lt_of_le i₁.1.isLt (Nat.le_add_right m n))⟩,
        ¬ (append init impl V₁ V₂ E₁ E₂ kSF₁ kSF₂ verify hVerify hsupp).toFun
          ⟨(i₁.1 : ℕ), by omega⟩ stmt
          (liftTranscript (pSpec₂ := pSpec₂) (i₁.1 : ℕ) i₁.1.isLt.le (by omega) T₁)
          ((Extractor.RoundByRound.appendOfPure E₁ E₂ rel₂ verify).extractMid
            (⟨(i₁.1 : ℕ), by omega⟩ : Fin (m + n)) stmt
            (Transcript.concat
              (cast (type_append_lt (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (i₁.1 : ℕ)
                i₁.1.isLt (by omega)).symm c₁)
              (liftTranscript (pSpec₂ := pSpec₂) (i₁.1 : ℕ) i₁.1.isLt.le (by omega) T₁)) witMid)
        ∧ (append init impl V₁ V₂ E₁ E₂ kSF₁ kSF₂ verify hVerify hsupp).toFun
            ⟨(i₁.1 : ℕ) + 1, by omega⟩ stmt
            (Transcript.concat
              (cast (type_append_lt (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (i₁.1 : ℕ)
                i₁.1.isLt (by omega)).symm c₁)
              (liftTranscript (pSpec₂ := pSpec₂) (i₁.1 : ℕ) i₁.1.isLt.le (by omega) T₁)) witMid)
      ↔ (∃ w₁ : WitMid₁ ⟨(i₁.1 : ℕ) + 1, Nat.succ_lt_succ i₁.1.isLt⟩,
          ¬ kSF₁ ⟨(i₁.1 : ℕ), by omega⟩ stmt T₁
            (E₁.extractMid ⟨(i₁.1 : ℕ), by omega⟩ stmt (Transcript.concat c₁ T₁) w₁)
          ∧ kSF₁ ⟨(i₁.1 : ℕ) + 1, by omega⟩ stmt (Transcript.concat c₁ T₁) w₁) := by
  rw [show Transcript.concat
        (cast (type_append_lt (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (i₁.1 : ℕ)
          i₁.1.isLt (by omega)).symm c₁)
        (liftTranscript (pSpec₂ := pSpec₂) (i₁.1 : ℕ) i₁.1.isLt.le (by omega) T₁)
      = liftTranscript (pSpec₂ := pSpec₂) ((i₁.1 : ℕ) + 1) (by omega) (by omega)
          (Transcript.concat c₁ T₁) from
    (liftTranscript_concat (pSpec₂ := pSpec₂) (i₁.1 : ℕ) i₁.1.isLt (by omega) T₁ c₁).symm]
  refine exists_cast_iff (Extractor.witMidAppend_le (WitMid₁ := WitMid₁) (WitMid₂ := WitMid₂)
    (r := (⟨(i₁.1 : ℕ) + 1,
      Nat.succ_lt_succ (lt_of_lt_of_le i₁.1.isLt (Nat.le_add_right m n))⟩ : Fin (m + n + 1)))
    i₁.1.isLt) fun witMid => ?_
  refine and_congr (not_congr ?_)
    (append_toFun_liftTranscript stmt ((i₁.1 : ℕ) + 1) i₁.1.isLt _ _)
  refine Iff.trans (append_toFun_liftTranscript stmt (i₁.1 : ℕ) i₁.1.isLt.le _ _) ?_
  rw [append_extractMid_lt (rel₂ := rel₂) (verify := verify) stmt (i₁.1 : ℕ) i₁.1.isLt
    (lt_of_lt_of_le i₁.1.isLt (Nat.le_add_right m n)) (Transcript.concat c₁ T₁) witMid]
  exact Iff.rfl

/-- **The bad-transition event past the cut implies the second component's.** At a round strictly
inside the second protocol the two events coincide. At the boundary round the composed state
function is still the *first* component's, and the implication is the contrapositive of the
boundary step: a second-component knowledge state that holds at round zero exhibits a witness for
the statement the first verifier reported, which `pickWit` then selects and the first component's
`toFun_full` accepts. -/
theorem event_inr_imp (stmt : Stmt₁) (w : ℕ) (hw : w < n)
    (T₁ : pSpec₁.FullTranscript) (T₂ : pSpec₂.Transcript ⟨w, by omega⟩)
    (msg : pSpec₂.«Type» ⟨w, hw⟩)
    (h : ∃ witMid : Extractor.WitMidAppend WitMid₁ WitMid₂ ⟨m + w + 1, by omega⟩,
        ¬ (append init impl V₁ V₂ E₁ E₂ kSF₁ kSF₂ verify hVerify hsupp).toFun
            ⟨m + w, by omega⟩ stmt (liftTranscriptR (pSpec₁ := pSpec₁) w hw.le T₁ T₂)
            ((Extractor.RoundByRound.appendOfPure E₁ E₂ rel₂ verify).extractMid
              (⟨m + w, by omega⟩ : Fin (m + n)) stmt
              (Transcript.concat
                (cast (type_append_add (pSpec₁ := pSpec₁) w hw (by omega)).symm msg)
                (liftTranscriptR (pSpec₁ := pSpec₁) w hw.le T₁ T₂)) witMid)
          ∧ (append init impl V₁ V₂ E₁ E₂ kSF₁ kSF₂ verify hVerify hsupp).toFun
              ⟨m + w + 1, by omega⟩ stmt
              (Transcript.concat
                (cast (type_append_add (pSpec₁ := pSpec₁) w hw (by omega)).symm msg)
                (liftTranscriptR (pSpec₁ := pSpec₁) w hw.le T₁ T₂)) witMid) :
    ∃ w₂ : WitMid₂ ⟨w + 1, by omega⟩,
      ¬ kSF₂ ⟨w, by omega⟩ (verify stmt T₁) T₂
          (E₂.extractMid ⟨w, hw⟩ (verify stmt T₁) (Transcript.concat msg T₂) w₂)
        ∧ kSF₂ ⟨w + 1, by omega⟩ (verify stmt T₁) (Transcript.concat msg T₂) w₂ := by
  obtain ⟨witMid, hnot, hyes⟩ := h
  refine ⟨cast (Extractor.witMid_index_cast (W := WitMid₂)
      (Fin.ext (show m + w + 1 - m = w + 1 by omega)))
    (cast (Extractor.witMidAppend_gt (WitMid₁ := WitMid₁)
      (r := (⟨m + w + 1, by omega⟩ : Fin (m + n + 1)))
      (show ¬ m + w + 1 ≤ m by omega)) witMid), ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos w with rfl | hw₀
    · -- The boundary round: the composed state function is still the first component's.
      obtain ⟨fb, hfb⟩ := heq_append_extractMid_boundary (E₁ := E₁) (E₂ := E₂) (rel₂ := rel₂)
        (verify := verify) stmt hw T₁ T₂ msg witMid
      rw [append_toFun_liftTranscriptR_zero stmt T₁ T₂ _] at hnot
      replace hnot : ¬ kSF₁ (Fin.last m) stmt T₁
          (E₁.extractOut stmt T₁ (Extractor.pickWit rel₂ (verify stmt T₁) fb)) := fun hc =>
        hnot ((congr_heq kSF₁ rfl stmt HEq.rfl
          ((cast_heq _ _).trans hfb)).mpr hc)
      intro hk
      refine hnot (kSF₁.toFun_full stmt T₁ _
        (probEvent_pos_of_pure verify hVerify hsupp stmt T₁ _
          (Extractor.pickWit_mem fb ⟨_, (kSF₂.toFun_empty _ _).mpr
            ((congr_heq kSF₂ (b := 0) rfl _
              (Transcript.heq_of_apply_heq rfl fun i hia _ => absurd hia (Nat.not_lt_zero i))
              HEq.rfl).mp hk)⟩)))
    · -- Strictly inside the second protocol.
      rw [append_toFun_liftTranscriptR stmt w hw.le hw₀ T₁ T₂ _] at hnot
      exact fun hc => hnot ((congr_heq kSF₂ rfl _ HEq.rfl
        ((cast_heq _ _).trans ((cast_heq _ _).trans
          (heq_append_extractMid_gt (E₁ := E₁) (E₂ := E₂) (rel₂ := rel₂)
            (verify := verify) stmt w hw hw₀ T₁ T₂ msg witMid)))).mpr hc)
  · rw [← liftTranscriptR_concat (pSpec₁ := pSpec₁) w hw T₁ T₂ msg] at hyes
    exact (append_toFun_liftTranscriptR stmt (w + 1) (by omega) (by omega) T₁
      (Transcript.concat msg T₂) _).mp hyes

end Readoff

end Verifier.KnowledgeStateFunction

namespace Prover

/-- `Prover.takeLeft` with the output witness type the *knowledge* game fixes. Round-by-round
knowledge soundness quantifies over provers whose output witness is the second relation's, where
plain round-by-round soundness quantifies over the type as well, so the split-off first half has to
report one. It never has to be *used*: the bad-transition game runs only `runToRound`, which never
calls `output`, and `takeLeftOut_runToRound` records that the rounds are unchanged. -/
def takeLeftOut (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtOut : Stmt₂) (witOut : Wit₂) : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁ where
  PrvState := fun i => P.PrvState (Prover.leftIdx n i)
  input := (P.takeLeft stmtOut).input
  sendMessage := (P.takeLeft stmtOut).sendMessage
  receiveChallenge := (P.takeLeft stmtOut).receiveChallenge
  output := fun _ => pure (stmtOut, witOut)

theorem takeLeftOut_runToRound (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (stmtOut : Stmt₂) (witOut : Wit₂) (i : Fin (m + 1)) (stmt : Stmt₁) (wit : Wit₁) :
    (P.takeLeftOut stmtOut witOut).runToRound i stmt wit
      = (P.takeLeft stmtOut).runToRound i stmt wit := rfl

/-- `Prover.dropLeftFrom`'s rounds are `Prover.dropLeft`'s from the state at the cut. The knowledge
game fixes the *input* witness type, so the second half has to take the cut state through `input`
rather than as its witness -- the dual of `takeLeftOut`. -/
theorem dropLeftFrom_runToRound {S W : Type}
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (w : P.PrvState (Prover.rightIdx m (0 : Fin (n + 1)))) (j : Fin (n + 1)) (s : S) (wit : W)
    (s' : Stmt₂) :
    (Prover.dropLeftFrom P w).runToRound j s wit
      = (P.dropLeft (Stmt₂ := Stmt₂)).runToRound j s' w := rfl

/-- **The prover's query log drops out of the bad-transition game.** The knowledge game carries the
log along and its event ignores it, so the event probability is the plain game's -- which is what
`Prover.rbrGame_inl` and `rbrGame_inr` split. -/
theorem probEvent_rbrKnowledgeGame_eq {N : ℕ} {pSpec : ProtocolSpec N} {S W S' W' σ : Type}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (impl' : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (P : Prover oSpec S W S' W' pSpec) (stmt : S) (wit : W) (i : pSpec.ChallengeIdx)
    (p : pSpec.Transcript i.1.castSucc × pSpec.Challenge i → Prop) (s₀ : σ) :
    Pr[fun x => p (x.1, x.2.1) | (simulateQ impl' (do
        let ⟨⟨transcript, _⟩, proveQueryLog⟩ ← P.runWithLogToRound i.1.castSucc stmt wit
        let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
        return (transcript, challenge, proveQueryLog))).run' s₀]
      = Pr[p | (simulateQ impl' (do
        let ⟨transcript, _⟩ ← P.runToRound i.1.castSucc stmt wit
        let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
        return (transcript, challenge))).run' s₀] := by
  have hmap : (do
        let ⟨transcript, _⟩ ← P.runToRound i.1.castSucc stmt wit
        let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
        return (transcript, challenge))
      = (fun x => (x.1, x.2.1)) <$> (do
        let ⟨⟨transcript, _⟩, proveQueryLog⟩ ← P.runWithLogToRound i.1.castSucc stmt wit
        let challenge ← liftComp (pSpec.getChallenge i) (oSpec + [pSpec.Challenge]ₒ)
        return (transcript, challenge, proveQueryLog)) := by
    rw [← Prover.runWithLogToRound_discard_log_eq_runToRound]
    simp only [map_bind, bind_map_left, map_pure]
  rw [hmap, probEvent_simulateQ_run'_map]
  rfl

end Prover

namespace Verifier

open scoped NNReal

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

set_option maxHeartbeats 1000000 in
theorem append_rbrKnowledgeSoundness_of_pure [Nonempty Stmt₂] [Nonempty Wit₂]
    (hst : impl.IsStateless) (hinit : Pr[⊥ | init] = 0)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ ε₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ ε₂) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  obtain ⟨WitMid₁, E₁, kSF₁, hK₁⟩ := h₁
  obtain ⟨WitMid₂, E₂, kSF₂, hK₂⟩ := h₂
  refine ⟨_, Extractor.RoundByRound.appendOfPure E₁ E₂ rel₂ verify,
    KnowledgeStateFunction.append init impl V₁ V₂ E₁ E₂ kSF₁ kSF₂ verify hVerify
      (support_nonempty_of_probFailure_eq_zero hinit), ?_⟩
  intro stmt witIn P i
  obtain ⟨stmtOut⟩ := ‹Nonempty Stmt₂›
  obtain ⟨witOut⟩ := ‹Nonempty Wit₂›
  by_cases hlt : ((i.1 : Fin (m + n)) : ℕ) < m
  · -- The challenge round lies inside the first protocol.
    obtain ⟨i₁, rfl⟩ : ∃ i₁ : pSpec₁.ChallengeIdx, i = ChallengeIdx.inl i₁ :=
      ⟨⟨⟨(i.1 : ℕ), hlt⟩, by
          rw [← dir_append_lt (pSpec₂ := pSpec₂) (i.1 : ℕ) hlt i.1.isLt]; exact i.2⟩,
        Subtype.ext (Fin.ext rfl)⟩
    simp only [Function.comp_apply, ChallengeIdx.sumEquiv_symm_inl, Sum.elim_inl]
    refine le_of_eq_of_le (Reduction.probEvent_bind_congr init fun s₀ =>
      Prover.probEvent_rbrKnowledgeGame_eq _ P stmt witIn (ChallengeIdx.inl i₁)
        (fun q => ∃ witMid,
          ¬ (KnowledgeStateFunction.append init impl V₁ V₂ E₁ E₂ kSF₁ kSF₂ verify hVerify
              (support_nonempty_of_probFailure_eq_zero hinit)).toFun
              (ChallengeIdx.inl i₁).1.castSucc stmt q.1
              ((Extractor.RoundByRound.appendOfPure E₁ E₂ rel₂ verify).extractMid
                (ChallengeIdx.inl i₁).1 stmt (Transcript.concat q.2 q.1) witMid)
            ∧ (KnowledgeStateFunction.append init impl V₁ V₂ E₁ E₂ kSF₁ kSF₂ verify hVerify
                (support_nonempty_of_probFailure_eq_zero hinit)).toFun
                (ChallengeIdx.inl i₁).1.succ stmt (Transcript.concat q.2 q.1) witMid) s₀) ?_
    rw [Prover.rbrGame_inl P stmtOut stmt witIn i₁]
    refine le_of_eq_of_le (Reduction.probEvent_bind_congr init fun s₀ => ?_)
      (hK₁ stmt witIn (P.takeLeftOut stmtOut witOut) i₁)
    rw [probEvent_simulateQ_run'_map]
    refine Eq.trans (probEvent_of_evalDist_eq (Reduction.evalDist_stateT_run'_congr
      (Reduction.evalDist_simulateQ_liftM_left _ s₀)) _) ?_
    refine Eq.trans ?_ (Prover.probEvent_rbrKnowledgeGame_eq _ (P.takeLeftOut stmtOut witOut)
      stmt witIn i₁
      (fun q => ∃ w₁, ¬ kSF₁ i₁.1.castSucc stmt q.1
          (E₁.extractMid i₁.1 stmt (Transcript.concat q.2 q.1) w₁)
        ∧ kSF₁ i₁.1.succ stmt (Transcript.concat q.2 q.1) w₁) s₀).symm
    exact congrArg _ (funext fun q => propext
      (KnowledgeStateFunction.event_inl stmt i₁ q.1 q.2))
  · -- The challenge round lies in the second protocol.
    obtain ⟨i₂, rfl⟩ : ∃ i₂ : pSpec₂.ChallengeIdx, i = ChallengeIdx.inr i₂ :=
      ⟨⟨⟨(i.1 : ℕ) - m, by omega⟩, by
          rw [← dir_append_ge (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (i.1 : ℕ) (by omega) i.1.isLt]
          exact i.2⟩,
        Subtype.ext (Fin.ext (show (i.1 : ℕ) = m + ((i.1 : ℕ) - m) by omega))⟩
    simp only [Function.comp_apply, ChallengeIdx.sumEquiv_symm_inr, Sum.elim_inr]
    refine le_of_eq_of_le (Reduction.probEvent_bind_congr init fun s₀ =>
      Prover.probEvent_rbrKnowledgeGame_eq _ P stmt witIn (ChallengeIdx.inr i₂)
        (fun q => ∃ witMid,
          ¬ (KnowledgeStateFunction.append init impl V₁ V₂ E₁ E₂ kSF₁ kSF₂ verify hVerify
              (support_nonempty_of_probFailure_eq_zero hinit)).toFun
              (ChallengeIdx.inr i₂).1.castSucc stmt q.1
              ((Extractor.RoundByRound.appendOfPure E₁ E₂ rel₂ verify).extractMid
                (ChallengeIdx.inr i₂).1 stmt (Transcript.concat q.2 q.1) witMid)
            ∧ (KnowledgeStateFunction.append init impl V₁ V₂ E₁ E₂ kSF₁ kSF₂ verify hVerify
                (support_nonempty_of_probFailure_eq_zero hinit)).toFun
                (ChallengeIdx.inr i₂).1.succ stmt (Transcript.concat q.2 q.1) witMid) s₀) ?_
    rw [Prover.rbrGame_inr P stmtOut stmt witIn i₂]
    refine probEvent_bind_phase_le _ _ _ fun p s₁ => ?_
    rw [probEvent_simulateQ_run'_map]
    refine le_of_eq_of_le (probEvent_of_evalDist_eq (Reduction.evalDist_stateT_run'_congr
      (Reduction.evalDist_simulateQ_liftM_right _ s₁)) _) ?_
    refine le_trans (probEvent_mono''
      (q := fun q : pSpec₂.Transcript i₂.1.castSucc × pSpec₂.Challenge i₂ =>
        ∃ w₂, ¬ kSF₂ i₂.1.castSucc (verify stmt p.1) q.1
            (E₂.extractMid i₂.1 (verify stmt p.1) (Transcript.concat q.2 q.1) w₂)
          ∧ kSF₂ i₂.1.succ (verify stmt p.1) (Transcript.concat q.2 q.1) w₂)
      fun q hq => KnowledgeStateFunction.event_inr_imp stmt (i₂.1 : ℕ) i₂.1.isLt p.1 q.1 q.2 hq) ?_
    rw [← probEvent_bind_run'_of_isStateless (hst.addLift challengeQueryImpl) hinit _ _ s₁]
    refine le_of_eq_of_le (Reduction.probEvent_bind_congr init fun s =>
      (Prover.probEvent_rbrKnowledgeGame_eq _
        (Prover.dropLeftFrom P (cast (Prover.takeLeft_prvState_cut P stmtOut) p.2))
        (verify stmt p.1) witOut i₂
        (fun q => ∃ w₂, ¬ kSF₂ i₂.1.castSucc (verify stmt p.1) q.1
            (E₂.extractMid i₂.1 (verify stmt p.1) (Transcript.concat q.2 q.1) w₂)
          ∧ kSF₂ i₂.1.succ (verify stmt p.1) (Transcript.concat q.2 q.1) w₂) s).symm) ?_
    exact hK₂ (verify stmt p.1) witOut
      (Prover.dropLeftFrom P (cast (Prover.takeLeft_prvState_cut P stmtOut) p.2)) i₂

end Verifier

section OracleProtocol

variable {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
  [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)] [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)} {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
  {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

namespace OracleVerifier

open scoped NNReal in
/-- Sequential composition preserves round-by-round knowledge soundness for oracle verifiers, for a
deterministic first verifier and a stateless handler. The oracle-side counterpart of
`Verifier.append_rbrKnowledgeSoundness_of_pure`; round-by-round knowledge soundness of an oracle
verifier is by definition that of the verifier underneath it. -/
theorem append_rbrKnowledgeSoundness_of_pure
    [Nonempty (Stmt₂ × ∀ i, OStmt₂ i)] [Nonempty Wit₂]
    (hst : impl.IsStateless) (hinit : Pr[⊥ | init] = 0)
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (verify : (Stmt₁ × ∀ i, OStmt₁ i) → pSpec₁.FullTranscript → (Stmt₂ × ∀ i, OStmt₂ i))
    (hVerify : V₁.toVerifier = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ ε₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ ε₂) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold rbrKnowledgeSoundness
  convert Verifier.append_rbrKnowledgeSoundness_of_pure hst hinit V₁.toVerifier V₂.toVerifier
    verify hVerify h₁ h₂
  simp only [append_toVerifier]

end OracleVerifier

end OracleProtocol
