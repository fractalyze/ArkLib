/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Batzorig Zorigoo
-/

import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# The state function of a sequential composition

`Verifier.StateFunction.append` used to sit in `Append.lean` with `toFun_next` and `toFun_full`
admitted. It is proved here, and its value past the cut is not what was written there.

**Past the cut it is the second component's state function, weakened by a disjunct.** The admitted
version read, at a round `r > m`, `S₁` at the *full* first transcript *and* `S₂` at the remaining
one. That conjunction does not satisfy `toFun_full`: `¬(S₁ ∧ S₂)` holds when `S₁` is false while
`S₂` is true, and a true `S₂` at a full transcript is exactly when `V₂` may output into `lang₃`, so
the required probability is not zero. `toFun_full` in fact pins the round-`m + n` value down to
something `S₂` implies, so the first component can only be consulted past the cut through a
*disjunct*. The value here is `S₂ (r - m) s₂ · ∨ s₂ ∈ lang₂`, where `s₂` is the statement `V₁`
reports at the cut.

**The disjunct is what a round-by-round bound past the cut needs.** `S₂` alone would not do. `V₂`'s
bad-transition bound is a hypothesis about statements *outside* `lang₂` only; on the branch where
the first half was broken -- `s₂ ∈ lang₂`, which a prover reaches with up to the first half's
accumulated error -- `S₂` is unconstrained and may flip at every round. Recording that branch as
"already true" takes it out of the bad-transition event, which becomes
`s₂ ∉ lang₂ ∧ ¬ S₂ w · ∧ S₂ (w + 1) ·` -- exactly what `V₂`'s hypothesis bounds. Dropping the
conjunct costs nothing in the other direction either: `S₁` false at the cut already forces `S₂`
false at round `0` of the second protocol, via `S₁.toFun_full` and `S₂.toFun_empty`, and that is
what carries the boundary round of `toFun_next`.

**An `init` that is actually sampled.** That boundary step reads `S₁.toFun_full`'s conclusion, a
statement about probability, as the set-level fact `verify stmt tr ∉ lang₂`
(`StateFunction.not_mem_of_pure`). A sampling with empty support makes every run fail and every
such probability zero, so the reading needs `hinit`. The same hypothesis appears in
`Verifier.append_soundness` for the same reason.

The deterministic-`V₁` hypothesis (`verify`, `hVerify`) is the one the admitted definition already
carried, and is the same one `Verifier.append_knowledgeSoundness_of_logIndependent` settled on.
-/

open OracleComp OracleSpec ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

namespace ProtocolSpec.Transcript

section Apply

/-! ### Reading a partial transcript at an explicit round number

The lemmas below are all stated at a raw `⟨i, _⟩` index rather than at a `Fin.castSucc` / `Fin.last`
one. That is what an appended protocol forces: its rounds are compared to the cut `m` by their
*value*, so every index in sight is an arithmetic expression, and `Fin.lastCases` has nothing to
match on. -/

variable {N : ℕ} {pSpec : ProtocolSpec N} {j : Fin N}

/-- `Transcript.concat` below the round it appends: the appended message is not read. -/
theorem concat_apply_of_lt (T : pSpec.Transcript j.castSucc) (msg : pSpec.«Type» j) (i : ℕ)
    (hi : i < (j : ℕ)) : Transcript.concat msg T ⟨i, Nat.lt_succ_of_lt hi⟩ = T ⟨i, hi⟩ :=
  Fin.snoc_castSucc (α := fun x : Fin ((j : ℕ) + 1) => pSpec.«Type» ⟨x.val, by omega⟩)
    (p := T) (x := msg) (i := ⟨i, hi⟩)

/-- `Transcript.concat` at the round it appends: the appended message is what is read. The two
sides live in `pSpec.Type ⟨i, _⟩` and `pSpec.Type j`, which are equal only once `i = j` is known,
hence `HEq`. -/
theorem concat_apply_last (T : pSpec.Transcript j.castSucc) (msg : pSpec.«Type» j) (i : ℕ)
    (h : i < (j : ℕ) + 1) (hi : ¬ i < (j : ℕ)) : HEq (Transcript.concat msg T ⟨i, h⟩) msg := by
  have hij : i = (j : ℕ) := by omega
  subst hij
  exact heq_of_eq (Fin.snoc_last
    (α := fun x : Fin ((j : ℕ) + 1) => pSpec.«Type» ⟨x.val, by omega⟩) (p := T) (x := msg))

/-- Two partial transcripts cut at equal rounds are `HEq` as soon as they agree at every round
number. The transcript-level companion of `Fin.ext`. -/
theorem heq_of_apply_heq {a b : Fin (N + 1)} (hab : a = b)
    {T : pSpec.Transcript a} {T' : pSpec.Transcript b}
    (h : ∀ (i : ℕ) (hia : i < (a : ℕ)) (hib : i < (b : ℕ)), HEq (T ⟨i, hia⟩) (T' ⟨i, hib⟩)) :
    HEq T T' := by
  subst hab
  exact heq_of_eq (funext fun i => eq_of_heq (h i.val i.isLt i.isLt))

end Apply

section Split

/-! ### Splitting a partial transcript of an appended protocol

`Transcript.fst` cuts the left half at `min k m`; a state function needs it cut at a round it names
itself -- at `k` while still inside the first protocol, and at `m` once past the cut -- so both cuts
get their own definition here. `Transcript.snd` is reused as is. -/

/-- The first `v` rounds of a partial transcript of `pSpec₁ ++ₚ pSpec₂`, as a partial transcript of
`pSpec₁`. Unlike `Transcript.fst` the cut is named by the caller, so no `min` appears in the
index. -/
def fstUpTo (v : ℕ) (hv : v ≤ m) {k : Fin (m + n + 1)} (hk : v ≤ (k : ℕ))
    (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) : pSpec₁.Transcript ⟨v, by omega⟩ :=
  fun i =>
    have hi : (i : ℕ) < v := i.isLt
    have hk' : (k : ℕ) < m + n + 1 := k.isLt
    cast (type_append_lt (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i.val (by omega) (by omega))
      (T ⟨i.val, by omega⟩)

/-- `fstUpTo m` at the cut, delivered as a *full* transcript of `pSpec₁` -- the same function, with
the type a deterministic first verifier must be applied to. It gets its own definition rather than
an ascription because `pSpec₁.Transcript ⟨m, _⟩` and `pSpec₁.FullTranscript` are not interchangeable
at `instances` transparency. -/
def fstFull {k : Fin (m + n + 1)} (hk : m ≤ (k : ℕ))
    (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) : pSpec₁.FullTranscript :=
  fun i =>
    have hi : (i : ℕ) < m := i.isLt
    have hk' : (k : ℕ) < m + n + 1 := k.isLt
    cast (type_append_lt (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) i.val (by omega) (by omega))
      (T ⟨i.val, by omega⟩)

theorem fstUpTo_apply_heq (v : ℕ) (hv : v ≤ m) {k : Fin (m + n + 1)} (hk : v ≤ (k : ℕ))
    (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) (i : ℕ) (hi : i < v) (h : i < (k : ℕ)) :
    HEq (fstUpTo v hv hk T ⟨i, hi⟩) (T ⟨i, h⟩) := cast_heq _ _

theorem fstFull_apply_heq {k : Fin (m + n + 1)} (hk : m ≤ (k : ℕ))
    (T : (pSpec₁ ++ₚ pSpec₂).Transcript k) (i : ℕ) (hi : i < m) (h : i < (k : ℕ)) :
    HEq (fstFull hk T ⟨i, hi⟩) (T ⟨i, h⟩) := cast_heq _ _

theorem snd_apply_heq {k : Fin (m + n + 1)} (T : (pSpec₁ ++ₚ pSpec₂).Transcript k)
    (i : ℕ) (hi : i < (k : ℕ) - m) (h : m + i < (k : ℕ)) :
    HEq (Transcript.snd T ⟨i, hi⟩) (T ⟨m + i, h⟩) := cast_heq _ _

/-- At the last round, the partial-transcript left half is the full-transcript one. -/
theorem fstFull_last (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    fstFull (k := Fin.last (m + n)) (by simp) tr = tr.fst := by
  funext i
  simp only [fstFull, FullTranscript.fst, eq_mp_eq_cast]
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _).symm)

/-- At the last round, the partial-transcript right half is the full-transcript one. The cuts are
`m + n - m` and `n`, equal but not definitionally so, hence `HEq`. -/
theorem heq_snd_last (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    HEq (Transcript.snd (k := Fin.last (m + n)) tr) tr.snd := by
  refine heq_of_apply_heq (b := Fin.last n) (Fin.ext (by simp)) fun i hia hib => ?_
  simp only [Transcript.snd, FullTranscript.snd, eq_mp_eq_cast]
  exact (cast_heq _ _).trans (cast_heq _ _).symm

end Split

end ProtocolSpec.Transcript

namespace Verifier.StateFunction

open ProtocolSpec.Transcript

section Lemmas

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- A state function does not distinguish transcripts that agree at every round number, even when
their cuts are only propositionally equal. -/
theorem congr_heq {N : ℕ} {A B : Type} {pSpec : ProtocolSpec N}
    {V : Verifier oSpec A B pSpec} {langIn : Set A} {langOut : Set B}
    (S : V.StateFunction init impl langIn langOut) {a b : Fin (N + 1)} (hab : a = b)
    (stmt : A) {T : pSpec.Transcript a} {T' : pSpec.Transcript b} (hT : HEq T T') :
    (S a stmt T ↔ S b stmt T') := by
  subst hab
  rw [eq_of_heq hT]

/-- `congr_heq` with the transcripts compared round by round. -/
theorem congr_apply {N : ℕ} {A B : Type} {pSpec : ProtocolSpec N}
    {V : Verifier oSpec A B pSpec} {langIn : Set A} {langOut : Set B}
    (S : V.StateFunction init impl langIn langOut) {a b : Fin (N + 1)} (hab : a = b)
    (stmt : A) {T : pSpec.Transcript a} {T' : pSpec.Transcript b}
    (h : ∀ (i : ℕ) (hia : i < (a : ℕ)) (hib : i < (b : ℕ)), HEq (T ⟨i, hia⟩) (T' ⟨i, hib⟩)) :
    (S a stmt T ↔ S b stmt T') :=
  congr_heq S hab stmt (heq_of_apply_heq hab h)

/-- **`toFun_full`, read at the set level, for a deterministic verifier.** A pure verifier's
verdict is reachable whenever `init` produces a seed, so "the output lands in `langOut` with
probability zero" says the verdict is not in `langOut`. Without `hinit` the probability is zero
for the uninteresting reason that the run never gets started. -/
theorem not_mem_of_pure {A B : Type} {N : ℕ} {pSpec : ProtocolSpec N}
    {V : Verifier oSpec A B pSpec} {langIn : Set A} {langOut : Set B}
    (S : V.StateFunction init impl langIn langOut)
    (verify : A → pSpec.FullTranscript → B) (hV : V = ⟨fun s t => pure (verify s t)⟩)
    (hinit : (support init).Nonempty) (stmt : A) (tr : pSpec.FullTranscript)
    (h : ¬ S (Fin.last N) stmt tr) : verify stmt tr ∉ langOut := by
  have key := S.toFun_full stmt tr h
  subst hV
  simp only [Verifier.run, StateT.run'_eq, OptionT.mk_bind, probEvent_eq_zero_iff, support_bind,
    OptionT.support_liftM, Set.mem_iUnion, OptionT.mem_support_iff, OptionT.run_mk, support_map,
    Set.mem_image, Prod.exists, exists_and_right, exists_eq_right, exists_prop,
    forall_exists_index, and_imp] at key
  obtain ⟨s, hs⟩ := hinit
  have heq :
      ((simulateQ impl (pure (verify stmt tr) : OptionT (OracleComp oSpec) B)).run s :
        ProbComp (Option B × σ)) = pure (some (verify stmt tr), s) := rfl
  exact key _ s hs s (by rw [heq]; simp)

end Lemmas

section Append

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}

/-- `omega`, with the `Fin.val` boilerplate of appended-round indices peeled off first. -/
local macro "fin_omega" : tactic =>
  `(tactic| first
      | omega
      | (simp only [Fin.val_mk, Fin.val_last, Fin.val_succ, Fin.val_castSucc]; omega))

/-- **The sequential composition of two state functions.** Before the cut it is the first
component's; past the cut it is the second component's, on the intermediate statement the
deterministic first verifier reports, or else that statement already being in `lang₂` -- which is
how a broken first half is recorded. See this file's module docstring for why it is that and not
the conjunction of the two, and for what `hinit` is doing. -/
def append
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂)
    (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    -- Assume the first verifier is deterministic for now
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hinit : (support init).Nonempty) :
      (V₁.append V₂).StateFunction init impl lang₁ lang₃ where
  toFun := fun roundIdx stmt₁ transcript =>
    if h : roundIdx.val ≤ m then
      -- Inside the first protocol: the first state function, on the transcript so far.
      S₁ ⟨roundIdx, by omega⟩ stmt₁ (fstUpTo roundIdx.val h le_rfl transcript)
    else
      -- Past the cut: the second state function, on the statement `V₁` reported at the cut --
      -- or that statement already being good, which is how a broken first half is recorded.
      S₂ ⟨roundIdx.val - m, by omega⟩
        (verify stmt₁ (fstFull (by omega) transcript))
        (Transcript.snd transcript)
      ∨ verify stmt₁ (fstFull (by omega) transcript) ∈ lang₂
  toFun_empty := by
    intro stmt
    rw [dif_pos (show ((0 : Fin (m + n + 1)) : ℕ) ≤ m by simp)]
    exact (S₁.toFun_empty stmt).trans
      (congr_apply S₁ (a := 0) rfl stmt fun i hia _ => absurd hia (Nat.not_lt_zero i))
  toFun_next := by
    intro k hDir stmt tr hnot msg
    by_cases h₁ : (k : ℕ) + 1 ≤ m
    · -- Both rounds lie inside the first protocol.
      have hk : (k : ℕ) < m := by omega
      rw [dif_pos (show ((k.succ : Fin (m + n + 1)) : ℕ) ≤ m by simpa using h₁)]
      rw [dif_pos (show ((k.castSucc : Fin (m + n + 1)) : ℕ) ≤ m by simpa using hk.le)] at hnot
      have hdir₁ : pSpec₁.dir ⟨(k : ℕ), hk⟩ = .P_to_V := by
        rw [← dir_append_lt (pSpec₂ := pSpec₂) (k : ℕ) hk k.isLt]; exact hDir
      have key := S₁.toFun_next ⟨(k : ℕ), hk⟩ hdir₁ stmt
        (fstUpTo ((k.castSucc : Fin (m + n + 1)) : ℕ) (by simpa using hk.le) le_rfl tr) hnot
        (cast (type_append_lt (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (k : ℕ) hk k.isLt) msg)
      intro hcon
      refine key ((congr_apply S₁ (b := ⟨((k.succ : Fin (m + n + 1)) : ℕ), by simpa using h₁⟩)
        rfl stmt ?_).mpr hcon)
      intro i hia hib
      simp only [fstUpTo, Transcript.concat, Fin.snoc, Fin.castLT]
      by_cases hi : i < (k : ℕ)
      · rw [dif_pos hi, dif_pos hi]
        exact ((cast_heq _ _).trans (cast_heq _ _)).trans (cast_heq _ _).symm
      · rw [dif_neg hi, dif_neg hi]
        exact ((cast_heq _ _).trans (cast_heq _ _)).trans
          ((cast_heq _ _).trans (cast_heq _ _)).symm
    · -- The new round lies in the second protocol.
      have hmk : m ≤ (k : ℕ) := by omega
      have hkn : (k : ℕ) < m + n := k.isLt
      have hsucc : ((k.succ : Fin (m + n + 1)) : ℕ) = (k : ℕ) + 1 := rfl
      have hcast : ((k.castSucc : Fin (m + n + 1)) : ℕ) = (k : ℕ) := rfl
      rw [dif_neg (show ¬ (((k.succ : Fin (m + n + 1)) : ℕ) ≤ m) from by fin_omega)]
      have hleft : fstFull (k := k.succ) (by fin_omega) (Transcript.concat msg tr)
          = fstFull (k := k.castSucc) (by fin_omega) tr := by
        funext i
        exact eq_of_heq
          (((fstFull_apply_heq _ _ (i : ℕ) i.isLt (by fin_omega)).trans
            (heq_of_eq (concat_apply_of_lt tr msg (i : ℕ) (by fin_omega)))).trans
            (fstFull_apply_heq _ _ (i : ℕ) i.isLt (by fin_omega)).symm)
      rw [hleft]
      by_cases hkm : (k : ℕ) = m
      · -- The boundary round: the first protocol has just ended.
        rw [dif_pos (show ((k.castSucc : Fin (m + n + 1)) : ℕ) ≤ m from by fin_omega)] at hnot
        have hn₀ : 0 < n := by fin_omega
        have h₂ : ¬ S₁ (Fin.last m) stmt (fstFull (k := k.castSucc) (by fin_omega) tr) := by
          intro hc
          refine hnot ((congr_apply S₁ (a := Fin.last m) (Fin.ext (by fin_omega)) stmt
            fun i hia hib => ?_).mp hc)
          exact (fstFull_apply_heq _ _ i hia (by fin_omega)).trans
            (fstUpTo_apply_heq _ _ _ _ i hib hib).symm
        have h₃ := not_mem_of_pure S₁ verify hVerify hinit stmt _ h₂
        have hk_eq : (⟨m + 0, by fin_omega⟩ : Fin (m + n)) = k := Fin.ext (by simp [hkm])
        have hdir₂ : pSpec₂.dir ⟨0, hn₀⟩ = .P_to_V := by
          rw [← dir_append_add (pSpec₁ := pSpec₁) 0 hn₀ (by fin_omega), hk_eq]
          exact hDir
        have key := S₂.toFun_next ⟨0, hn₀⟩ hdir₂ _ (fun i => Fin.elim0 i)
          (fun hc => h₃ ((S₂.toFun_empty _).mpr hc))
          (cast (type_append_add (pSpec₁ := pSpec₁) 0 hn₀ (by fin_omega))
            (cast (congrArg (pSpec₁ ++ₚ pSpec₂).Type hk_eq.symm) msg))
        intro hcon
        refine key ((congr_heq S₂ (Fin.ext (by fin_omega)) _ ?_).mpr (hcon.resolve_right h₃))
        refine heq_of_apply_heq (Fin.ext (by fin_omega)) fun i hia hib => ?_
        have hia' : i < 0 + 1 := hia
        have hib' : i < (k : ℕ) + 1 - m := hib
        exact ((concat_apply_last _ _ i hia' (Nat.not_lt_zero i)).trans
          ((cast_heq _ _).trans (cast_heq _ _))).trans
          (((snd_apply_heq _ i hib (by fin_omega)).trans
            (concat_apply_last tr msg (m + i) (by fin_omega) (by fin_omega))).symm)
      · -- Strictly inside the second protocol.
        have hmk' : m < (k : ℕ) := by fin_omega
        rw [dif_neg (show ¬ (((k.castSucc : Fin (m + n + 1)) : ℕ) ≤ m) from by fin_omega)] at hnot
        have hdir₂ : pSpec₂.dir ⟨(k : ℕ) - m, by fin_omega⟩ = .P_to_V := by
          rw [← dir_append_ge (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (k : ℕ) hmk k.isLt]
          exact hDir
        have key := S₂.toFun_next ⟨(k : ℕ) - m, by fin_omega⟩ hdir₂ _ (Transcript.snd tr)
          (fun hc => hnot (Or.inl hc))
          (cast (type_append_ge (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) (k : ℕ) hmk k.isLt) msg)
        intro hcon
        refine key ((congr_heq S₂ (Fin.ext (by fin_omega)) _ ?_).mpr
          (hcon.resolve_right fun hc => hnot (Or.inr hc)))
        refine heq_of_apply_heq (Fin.ext (by fin_omega)) fun i hia hib => ?_
        have hia' : i < (k : ℕ) - m + 1 := hia
        have hib' : i < (k : ℕ) + 1 - m := hib
        by_cases hi : i < (k : ℕ) - m
        · exact ((heq_of_eq (concat_apply_of_lt _ _ i hi)).trans
            (snd_apply_heq tr i hi (by fin_omega))).trans
            (((snd_apply_heq _ i hib (by fin_omega)).trans
              (heq_of_eq (concat_apply_of_lt tr msg (m + i) (by fin_omega)))).symm)
        · exact ((concat_apply_last _ _ i hia' hi).trans (cast_heq _ _)).trans
            (((snd_apply_heq _ i hib (by fin_omega)).trans
              (concat_apply_last tr msg (m + i) (by fin_omega) (by fin_omega))).symm)
  toFun_full := by
    intro stmt (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) hnot
    have hrun : ((V₁.append V₂).run stmt tr) = V₂.run (verify stmt tr.fst) tr.snd := by
      subst hVerify; simp [Verifier.append, Verifier.run]
    rw [hrun]
    refine S₂.toFun_full (verify stmt tr.fst) tr.snd ?_
    by_cases hn : ((Fin.last (m + n) : Fin (m + n + 1)) : ℕ) ≤ m
    · -- The second protocol has no rounds at all.
      rw [dif_pos hn] at hnot
      have hn₀ : n = 0 := by simpa using hn
      subst hn₀
      have h₂ : ¬ S₁ (Fin.last m) stmt tr.fst := by
        intro hc
        refine hnot ((congr_apply S₁ (a := Fin.last m) (Fin.ext (by simp)) stmt
          fun i hia hib => ?_).mp hc)
        simp only [FullTranscript.fst, fstUpTo, eq_mp_eq_cast]
        exact (cast_heq _ _).trans (cast_heq _ _).symm
      have h₃ := not_mem_of_pure S₁ verify hVerify hinit stmt _ h₂
      intro hc
      exact h₃ ((S₂.toFun_empty _).mpr
        ((congr_apply S₂ (a := Fin.last 0) (b := 0) (Fin.ext (by simp)) _
          fun i hia _ => absurd hia (by simp)).mp hc))
    · rw [dif_neg hn, fstFull_last] at hnot
      intro hc
      exact hnot (Or.inl ((congr_heq S₂ (a := Fin.last n) (Fin.ext (by simp))
        (verify stmt tr.fst) (heq_snd_last tr).symm).mp hc))

end Append

end Verifier.StateFunction
