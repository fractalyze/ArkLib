/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Composition.Sequential.AppendRbrSoundness

/-!
# Composing a round-by-round extractor and knowledge state function

`Verifier.append_rbrKnowledgeSoundness` is still admitted in `Append.lean`. Round-by-round
knowledge soundness asks for three objects rather than one, and this file builds two of them for a
deterministic first verifier: `Extractor.RoundByRound.appendOfPure` and
`Verifier.KnowledgeStateFunction.append`.

The shape follows `AppendStateFunction.lean`'s, one level up. The intermediate-witness family
(`Extractor.WitMidAppend`) is the first extractor's up to and including the cut and the second's
past it; the cut is the first family's *last* stage, which is exactly where the first extractor
takes a `Wit₂` in, and the second extractor's round-zero stage is a `Wit₂` by its own `eqIn`. The
knowledge state function is the first component's before the cut and, past it, the second's on the
statement the first verifier reported -- or else that statement already having a witness, the same
"the first half was broken" disjunct the language-level version needs, and for the same reason.

The boundary round is the only interesting one. Going from round `m + 1` back to round `m` the
extractor has to hand the first component a `Wit₂`, and the first component's `toFun_full` will only
accept one that is actually related to the statement the first verifier reported. Both sides of the
disjunct say such a witness exists -- the left one via the second knowledge state function's own
`toFun_next` and `toFun_empty` -- so `Extractor.pickWit` selects one classically, exactly as
`Extractor.RoundByRoundOneShot.toRoundByRoundOfRel` already does.
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

/-- The sequential composition of two knowledge state functions, for a deterministic first
verifier. -/
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
        ∨ ∃ v, (verify stmt (Transcript.fstFull (by omega) tr), v) ∈ rel₂
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
          rcases h with h | h
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
          · exact h
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
        rcases h with h | h
        · left
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
        · right; exact h
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
      exact Or.inl ((congr_heq kSF₂ (Fin.ext (show (n : ℕ) = m + n - m by omega)) _
        (Transcript.heq_snd_last tr).symm (cast_heq _ _).symm).mp hfull₂)

end Verifier.KnowledgeStateFunction
