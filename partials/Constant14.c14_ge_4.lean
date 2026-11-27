import FormalConjectures.OptimizationConstants.«14»

-- Problem: Tao's Optimization Constant 14 / Smallest $n$ for which the value of $BB(n)$ is undecidable — c14 ge 4
-- Upstream: formal-conjectures FormalConjectures/OptimizationConstants/14.lean:1729 (declaration Constant14.c14_ge_4)
-- Credit: @mucoucah (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- STATUS: unfinished. `OMA.solution` is proved from four named gaps (C14Aux.gap_*), each a sorry:
--   gap_sigma1_complete   halting machines with at most 3 states are provably halting in ZFC;
--   gap_small_nonhalting  non-halting machines with at most 3 states are provably non-halting;
--   gap_standard_model    a non-halting machine falsifies `halts M` in the model ZFSet;
--   gap_goedel            some non-halting machine has ZFC-unprovable non-halting (Goedel).
-- Verified below (no sorry in any of these):
--   C14Sem.sound / unprovable_of_model : soundness of the copied LK system for Tarski semantics;
--   C14Model.zfsetModel / zfc_consistent : ZFSet is a model of the formalized ZFC;
--   C14Faith.ev_nff0/1/2, ev_nf1/2 : general evaluation of the nested function-term notation;
--   C14Faith.ev_pi1, ev_pi2, ev_value_fn, ev_integerSucc, ev_integerPred, ev_nextConfig,
--     ev_nextStep, ev_orbit_fn, ev_initialConfig_fn, ev_halts, exists_table, halts_sem :
--     the ZFSet meaning of every piece of the encoding, up to `halts M` itself;
--   C14Faith.tr_iff_ev : any Tarski truth predicate on ZFSet agrees with `ev`.
-- The same four-way split is the checker-accepted reduction kept in
-- .oma/scratch/reductions/Constant14.c14_ge_4.R1.lean (its main carries soundness and the model).

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory Turing BusyBeaver


namespace C14Sem

variable {D : Type*} (R : ∀ {k : ℕ}, (ℒₛₑₜ).Rel k → (Fin k → D) → Prop)

def tval {ξ : Type*} {n : ℕ} (e : Fin n → D) (ε : ξ → D) : Semiterm ℒₛₑₜ ξ n → D
  | .bvar i => e i
  | .fvar x => ε x
  | .func f _ => (f : Empty).elim

def ev {ξ : Type*} : ∀ {n : ℕ}, (Fin n → D) → (ξ → D) → Semiformula ℒₛₑₜ ξ n → Prop
  | _, _, _, .verum => True
  | _, _, _, .falsum => False
  | _, e, ε, .rel r v => R r (fun i => tval e ε (v i))
  | _, e, ε, .nrel r v => ¬ R r (fun i => tval e ε (v i))
  | _, e, ε, .and φ ψ => ev e ε φ ∧ ev e ε ψ
  | _, e, ε, .or φ ψ => ev e ε φ ∨ ev e ε ψ
  | _, e, ε, .all φ => ∀ d, ev (Matrix.vecCons d e) ε φ
  | _, e, ε, .exs φ => ∃ d, ev (Matrix.vecCons d e) ε φ

lemma ev_neg {ξ : Type*} {n : ℕ} (e : Fin n → D) (ε : ξ → D) (φ : Semiformula ℒₛₑₜ ξ n) :
    ev R e ε (Semiformula.neg φ) ↔ ¬ ev R e ε φ := by
  induction φ with
  | verum => simp [Semiformula.neg, ev]
  | falsum => simp [Semiformula.neg, ev]
  | rel r v => simp [Semiformula.neg, ev]
  | nrel r v => simp [Semiformula.neg, ev]
  | and φ ψ ih1 ih2 => simp only [Semiformula.neg, ev, ih1, ih2]; tauto
  | or φ ψ ih1 ih2 => simp only [Semiformula.neg, ev, ih1, ih2]; tauto
  | all φ ih => simp only [Semiformula.neg, ev, ih]; push Not; rfl
  | exs φ ih => simp only [Semiformula.neg, ev, ih]; push Not; rfl

lemma tval_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    (e : Fin n₂ → D) (ε : ξ₂ → D) (t : Semiterm ℒₛₑₜ ξ₁ n₁) :
    tval e ε (ω t) = tval (fun i => tval e ε (ω (Semiterm.bvar i)))
      (fun x => tval e ε (ω (Semiterm.fvar x))) t := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func f v => exact (f : Empty).elim

lemma tval_bShift {ξ : Type*} {n : ℕ} (d : D) (e : Fin n → D) (ε : ξ → D)
    (t : Semiterm ℒₛₑₜ ξ n) :
    tval (Matrix.vecCons d e) ε (Rew.bShift t) = tval e ε t := by
  cases t with
  | bvar i => rfl
  | fvar x => rfl
  | func f v => exact (f : Empty).elim

lemma tval_q {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂)
    (d : D) (e : Fin n₂ → D) (ε : ξ₂ → D) :
    (fun i => tval (Matrix.vecCons d e) ε (ω.q (Semiterm.bvar i))) =
      Matrix.vecCons d (fun i => tval e ε (ω (Semiterm.bvar i))) ∧
    (fun x => tval (Matrix.vecCons d e) ε (ω.q (Semiterm.fvar x))) =
      (fun x => tval e ε (ω (Semiterm.fvar x))) := by
  constructor
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact tval_bShift d e ε (ω (Semiterm.bvar j))
  · funext x
    exact tval_bShift d e ε (ω (Semiterm.fvar x))

lemma ev_rew {ξ₁ ξ₂ : Type*} {n₁ : ℕ} (φ : Semiformula ℒₛₑₜ ξ₁ n₁) :
    ∀ {n₂ : ℕ} (ω : Rew ℒₛₑₜ ξ₁ n₁ ξ₂ n₂) (e : Fin n₂ → D) (ε : ξ₂ → D),
    ev R e ε (Semiformula.rewAux ω φ) ↔ ev R (fun i => tval e ε (ω (Semiterm.bvar i)))
      (fun x => tval e ε (ω (Semiterm.fvar x))) φ := by
  induction φ with
  | verum => intros; exact Iff.rfl
  | falsum => intros; exact Iff.rfl
  | rel r v =>
    intro n₂ ω e ε
    show R r _ ↔ R r _
    have h : (fun i => tval e ε ((ω ∘ v) i)) = (fun i => tval (fun i => tval e ε (ω (Semiterm.bvar i)))
      (fun x => tval e ε (ω (Semiterm.fvar x))) (v i)) := funext fun i => tval_rew ω e ε (v i)
    rw [h]
  | nrel r v =>
    intro n₂ ω e ε
    show ¬ R r _ ↔ ¬ R r _
    have h : (fun i => tval e ε ((ω ∘ v) i)) = (fun i => tval (fun i => tval e ε (ω (Semiterm.bvar i)))
      (fun x => tval e ε (ω (Semiterm.fvar x))) (v i)) := funext fun i => tval_rew ω e ε (v i)
    rw [h]
  | and φ ψ ih1 ih2 =>
    intro n₂ ω e ε
    exact and_congr (ih1 ω e ε) (ih2 ω e ε)
  | or φ ψ ih1 ih2 =>
    intro n₂ ω e ε
    exact or_congr (ih1 ω e ε) (ih2 ω e ε)
  | all φ ih =>
    intro n₂ ω e ε
    show (∀ d, _) ↔ (∀ d, _)
    refine forall_congr' fun d => ?_
    rw [ih ω.q (Matrix.vecCons d e) ε, (tval_q ω d e ε).1, (tval_q ω d e ε).2]
  | exs φ ih =>
    intro n₂ ω e ε
    show (∃ d, _) ↔ (∃ d, _)
    refine exists_congr fun d => ?_
    rw [ih ω.q (Matrix.vecCons d e) ε, (tval_q ω d e ε).1, (tval_q ω d e ε).2]


lemma mem_atom {α : Type*} {a x : α} : x ∈ Multiset.atom a ↔ x = a := Multiset.mem_singleton

def Valid (Γ : Sequent ℒₛₑₜ) : Prop :=
  ∀ ε : ℕ → D, ∃ φ ∈ Γ, ev R (Fin.elim0 : Fin 0 → D) ε φ

lemma ev_e0 {ξ : Type*} (e e' : Fin 0 → D) (ε : ξ → D) (φ : Semiformula ℒₛₑₜ ξ 0) :
    ev R e ε φ ↔ ev R e' ε φ := by
  rw [Subsingleton.elim e e']

lemma ev_shift {n : ℕ} (e : Fin n → D) (ε : ℕ → D) (φ : Semiproposition ℒₛₑₜ n) :
    ev R e ε (Rewriting.shift φ) ↔ ev R e (fun k => ε (k + 1)) φ := by
  show ev R e ε (Semiformula.rewAux Rew.shift φ) ↔ _
  rw [ev_rew]
  exact Iff.rfl

lemma ev_free (e : Fin 0 → D) (ε : ℕ → D) (φ : Semiproposition ℒₛₑₜ (0 + 1)) :
    ev R e ε (Rewriting.free φ) ↔ ev R (Matrix.vecCons (ε 0) e) (fun k => ε (k + 1)) φ := by
  show ev R e ε (Semiformula.rewAux Rew.free φ) ↔ _
  rw [ev_rew]
  have h : (fun i : Fin (0 + 1) => tval e ε (Rew.free (Semiterm.bvar i) : Semiterm ℒₛₑₜ ℕ 0)) =
      Matrix.vecCons (ε 0) e := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    rfl
  rw [h]
  exact Iff.rfl

lemma ev_subst1 (e : Fin 0 → D) (ε : ℕ → D) (φ : Semiproposition ℒₛₑₜ (0 + 1))
    (t : Semiterm ℒₛₑₜ ℕ 0) :
    ev R e ε (φ ⇜ ![t]) ↔ ev R (Matrix.vecCons (tval e ε t) e) ε φ := by
  show ev R e ε (Semiformula.rewAux (Rew.subst ![t]) φ) ↔ _
  rw [ev_rew]
  have h : (fun i : Fin (0 + 1) => tval e ε (Rew.subst ![t] (Semiterm.bvar i) : Semiterm ℒₛₑₜ ℕ 0)) =
      Matrix.vecCons (tval e ε t) e := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    rfl
  rw [h]
  exact Iff.rfl

theorem sound {Γ : Sequent ℒₛₑₜ} (d : Derivation Γ) : Valid R Γ := by
  induction d with
  | identity r v =>
    intro ε
    by_cases h : ev R (Fin.elim0 : Fin 0 → D) ε (Semiformula.rel r v)
    · exact ⟨_, Multiset.mem_add.2 (Or.inl (mem_atom.2 rfl)), h⟩
    · exact ⟨Semiformula.nrel r v, Multiset.mem_add.2 (Or.inr (mem_atom.2 rfl)), h⟩
  | cut d1 d2 ih1 ih2 =>
    rename_i Γ φ Δ
    intro ε
    obtain ⟨χ1, h1, e1⟩ := ih1 ε
    obtain ⟨χ2, h2, e2⟩ := ih2 ε
    rcases Multiset.mem_add.1 h1 with h1 | h1
    · exact ⟨χ1, Multiset.mem_add.2 (Or.inl h1), e1⟩
    rcases Multiset.mem_add.1 h2 with h2 | h2
    · exact ⟨χ2, Multiset.mem_add.2 (Or.inr h2), e2⟩
    rw [mem_atom] at h1 h2
    subst h1 h2
    exact absurd e1 ((ev_neg R _ _ _).1 e2)
  | contraction d hsub ih =>
    intro ε
    obtain ⟨χ, h, e⟩ := ih ε
    exact ⟨χ, hsub h, e⟩
  | verum =>
    intro ε
    exact ⟨_, mem_atom.2 rfl, trivial⟩
  | or d ih =>
    rename_i Γ φ ψ
    intro ε
    obtain ⟨χ, h, e⟩ := ih ε
    rcases Multiset.mem_add.1 h with h | h
    · exact ⟨χ, Multiset.mem_add.2 (Or.inl h), e⟩
    · refine ⟨φ ⋎ ψ, Multiset.mem_add.2 (Or.inr (mem_atom.2 rfl)), ?_⟩
      rcases Multiset.mem_add.1 h with h | h
      · rw [mem_atom] at h; subst h; exact Or.inl e
      · rw [mem_atom] at h; subst h; exact Or.inr e
  | and d1 d2 ih1 ih2 =>
    rename_i Γ φ ψ
    intro ε
    obtain ⟨χ1, h1, e1⟩ := ih1 ε
    obtain ⟨χ2, h2, e2⟩ := ih2 ε
    rcases Multiset.mem_add.1 h1 with h1 | h1
    · exact ⟨χ1, Multiset.mem_add.2 (Or.inl h1), e1⟩
    rcases Multiset.mem_add.1 h2 with h2 | h2
    · exact ⟨χ2, Multiset.mem_add.2 (Or.inl h2), e2⟩
    rw [mem_atom] at h1 h2
    subst h1 h2
    exact ⟨_, Multiset.mem_add.2 (Or.inr (mem_atom.2 rfl)), ⟨e1, e2⟩⟩
  | all d ih =>
    rename_i Γ φ
    intro ε
    by_cases hΓ : ∃ χ ∈ Γ, ev R (Fin.elim0 : Fin 0 → D) ε χ
    · obtain ⟨χ, h, e⟩ := hΓ
      exact ⟨χ, Multiset.mem_add.2 (Or.inl h), e⟩
    refine ⟨∀¹ φ, Multiset.mem_add.2 (Or.inr (mem_atom.2 rfl)), ?_⟩
    intro x
    let ε' : ℕ → D := fun k => Nat.casesOn k x ε
    obtain ⟨χ, h, e⟩ := ih ε'
    rcases Multiset.mem_add.1 h with h | h
    · obtain ⟨ψ, hψ, rfl⟩ := Multiset.mem_map.1 h
      exact absurd ⟨ψ, hψ, (ev_shift R _ ε' ψ).1 e⟩ hΓ
    · rw [mem_atom] at h
      subst h
      exact (ev_free R _ ε' φ).1 e
  | exs d ih =>
    rename_i Γ φ t
    intro ε
    obtain ⟨χ, h, e⟩ := ih ε
    rcases Multiset.mem_add.1 h with h | h
    · exact ⟨χ, Multiset.mem_add.2 (Or.inl h), e⟩
    · rw [mem_atom] at h
      subst h
      exact ⟨∃¹ φ, Multiset.mem_add.2 (Or.inr (mem_atom.2 rfl)),
        ⟨tval (Fin.elim0 : Fin 0 → D) ε t, (ev_subst1 R _ ε φ t).1 e⟩⟩

def SatS (σ : Sentence ℒₛₑₜ) : Prop := ev R (Fin.elim0 : Fin 0 → D) (Empty.elim : Empty → D) σ

lemma ev_emb {n : ℕ} (e : Fin n → D) (ε : ℕ → D) (σ : Semisentence ℒₛₑₜ n) :
    ev R e ε (Rewriting.emb σ : Semiproposition ℒₛₑₜ n) ↔ ev R e (Empty.elim : Empty → D) σ := by
  show ev R e ε (Semiformula.rewAux Rew.emb σ) ↔ _
  rw [ev_rew]
  have h : (fun x : Empty => tval e ε (Rew.emb (Semiterm.fvar x) : Semiterm ℒₛₑₜ ℕ n)) =
      (Empty.elim : Empty → D) := funext fun x => x.elim
  rw [h]
  exact Iff.rfl

theorem sound_theory [Nonempty D] {T : Theory ℒₛₑₜ} {σ : Sentence ℒₛₑₜ}
    (hT : ∀ ψ ∈ T, SatS R ψ) (h : FFL.Entailment.Provable T σ) : SatS R σ := by
  obtain ⟨pf⟩ := h
  have hv := sound R pf.derivation (fun _ => Classical.arbitrary D)
  obtain ⟨χ, hχ, he⟩ := hv
  obtain ⟨χ0, h0, rfl⟩ := Multiset.mem_map.1 hχ
  rw [ev_emb] at he
  rcases Multiset.mem_add.1 h0 with h0 | h0
  · rw [mem_atom] at h0
    subst h0
    exact (ev_e0 R _ _ _ _).1 he
  · obtain ⟨ψ, hψ, rfl⟩ := Multiset.mem_map.1 h0
    have := (ev_neg R _ _ ψ).1 he
    exact absurd ((ev_e0 R _ _ _ _).1 (hT ψ (pf.axioms_mem ψ hψ))) this

theorem unprovable_of_model [Nonempty D] {T : Theory ℒₛₑₜ} {σ : Sentence ℒₛₑₜ}
    (hT : ∀ ψ ∈ T, SatS R ψ) (hσ : ¬ SatS R σ) : T ⊬ σ :=
  fun h => hσ (sound_theory R hT h)

end C14Sem


namespace C14Model

open C14Sem

def zR : ∀ {k : ℕ}, Language.Set.Rel k → (Fin k → ZFSet.{0}) → Prop
  | _, .eq, v => v 0 = v 1
  | _, .mem, v => v 0 ∈ v 1

abbrev R' : ∀ {k : ℕ}, (ℒₛₑₜ).Rel k → (Fin k → ZFSet.{0}) → Prop := fun r v => zR r v

lemma ev_eq {ξ : Type*} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) (t u : Semiterm ℒₛₑₜ ξ n) :
    ev R' e ε (Semiformula.Operator.operator Semiformula.Operator.Eq.eq ![t, u]) ↔ tval e ε t = tval e ε u := by
  show ev R' e ε (Semiformula.rewAux _ (Semiformula.rewAux _ _)) ↔ _
  rw [ev_rew, ev_rew]
  exact Iff.rfl

lemma ev_mem {ξ : Type*} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0}) (t u : Semiterm ℒₛₑₜ ξ n) :
    ev R' e ε (Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![t, u]) ↔ tval e ε t ∈ tval e ε u := by
  show ev R' e ε (Semiformula.rewAux _ (Semiformula.rewAux _ _)) ↔ _
  rw [ev_rew, ev_rew]
  exact Iff.rfl


section simpset
variable {ξ : Type*} {n : ℕ} (e : Fin n → ZFSet.{0}) (ε : ξ → ZFSet.{0})

@[simp] lemma tval_bvar (i : Fin n) : tval e ε (Semiterm.bvar i : Semiterm ℒₛₑₜ ξ n) = e i := rfl
@[simp] lemma tval_fvar (x : ξ) : tval e ε (Semiterm.fvar x : Semiterm ℒₛₑₜ ξ n) = ε x := rfl
@[simp] lemma ev_and' (φ ψ : Semiformula ℒₛₑₜ ξ n) : ev R' e ε (φ ⋏ ψ) ↔ ev R' e ε φ ∧ ev R' e ε ψ := Iff.rfl
@[simp] lemma ev_or' (φ ψ : Semiformula ℒₛₑₜ ξ n) : ev R' e ε (φ ⋎ ψ) ↔ ev R' e ε φ ∨ ev R' e ε ψ := Iff.rfl
@[simp] lemma ev_not' (φ : Semiformula ℒₛₑₜ ξ n) : ev R' e ε (∼φ) ↔ ¬ ev R' e ε φ := ev_neg R' e ε φ
@[simp] lemma ev_imp' (φ ψ : Semiformula ℒₛₑₜ ξ n) : ev R' e ε (φ 🡒 ψ) ↔ (ev R' e ε φ → ev R' e ε ψ) := by
  show ev R' e ε (Semiformula.or (Semiformula.neg φ) ψ) ↔ _
  show ev R' e ε (Semiformula.neg φ) ∨ ev R' e ε ψ ↔ _
  rw [ev_neg]; tauto
@[simp] lemma ev_iff' (φ ψ : Semiformula ℒₛₑₜ ξ n) : ev R' e ε (φ 🡘 ψ) ↔ (ev R' e ε φ ↔ ev R' e ε ψ) := by
  show ev R' e ε ((φ 🡒 ψ) ⋏ (ψ 🡒 φ)) ↔ _
  rw [ev_and', ev_imp', ev_imp']; tauto
@[simp] lemma ev_all' (φ : Semiformula ℒₛₑₜ ξ (n + 1)) : ev R' e ε (∀¹ φ) ↔ ∀ d, ev R' (Matrix.vecCons d e) ε φ := Iff.rfl
@[simp] lemma ev_exs' (φ : Semiformula ℒₛₑₜ ξ (n + 1)) : ev R' e ε (∃¹ φ) ↔ ∃ d, ev R' (Matrix.vecCons d e) ε φ := Iff.rfl
@[simp] lemma ev_top' : ev R' e ε (⊤ : Semiformula ℒₛₑₜ ξ n) ↔ True := Iff.rfl
@[simp] lemma ev_subst' {m : ℕ} (φ : Semiformula ℒₛₑₜ ξ m) (v : Fin m → Semiterm ℒₛₑₜ ξ n) :
    ev R' e ε (φ ⇜ v) ↔ ev R' (fun i => tval e ε (v i)) ε φ := by
  show ev R' e ε (Semiformula.rewAux _ φ) ↔ _
  rw [ev_rew]; exact Iff.rfl
@[simp] lemma ev_eq' (t u : Semiterm ℒₛₑₜ ξ n) :
    ev R' e ε (Semiformula.Operator.operator Semiformula.Operator.Eq.eq ![t, u]) ↔ tval e ε t = tval e ε u :=
  ev_eq e ε t u
@[simp] lemma ev_mem' (t u : Semiterm ℒₛₑₜ ξ n) :
    ev R' e ε (Semiformula.Operator.operator Semiformula.Operator.Mem.mem ![t, u]) ↔ tval e ε t ∈ tval e ε u :=
  ev_mem e ε t u
@[simp] lemma ev_ballMem (t : Semiterm ℒₛₑₜ ξ n) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    ev R' e ε (Semiformula.ballMem t φ) ↔ ∀ d ∈ tval e ε t, ev R' (Matrix.vecCons d e) ε φ := by
  show ev R' e ε (∀¹ _) ↔ _
  rw [ev_all']
  refine forall_congr' fun d => ?_
  rw [ev_imp', ev_mem']
  simp [tval_bShift]
@[simp] lemma ev_bexsMem (t : Semiterm ℒₛₑₜ ξ n) (φ : Semiformula ℒₛₑₜ ξ (n + 1)) :
    ev R' e ε (Semiformula.bexsMem t φ) ↔ ∃ d ∈ tval e ε t, ev R' (Matrix.vecCons d e) ε φ := by
  show ev R' e ε (∃¹ _) ↔ _
  rw [ev_exs']
  refine exists_congr fun d => ?_
  show ev R' _ ε (Semiformula.and _ _) ↔ _
  show ev R' _ ε _ ∧ ev R' _ ε _ ↔ _
  rw [ev_mem']
  simp [tval_bShift]
@[simp] lemma ev_rel_eq (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    ev R' e ε (Semiformula.rel Language.Set.Rel.eq v) ↔ tval e ε (v 0) = tval e ε (v 1) := Iff.rfl
@[simp] lemma ev_rel_mem (v : Fin 2 → Semiterm ℒₛₑₜ ξ n) :
    ev R' e ε (Semiformula.rel Language.Set.Rel.mem v) ↔ tval e ε (v 0) ∈ tval e ε (v 1) := Iff.rfl
end simpset

lemma sat_empty : SatS R' Axiom.empty := by
  unfold SatS Axiom.empty
  simp
  exact ⟨∅, fun y => ZFSet.notMem_empty y⟩

lemma sat_ext : SatS R' Axiom.extentionality := by
  unfold SatS Axiom.extentionality
  simp
  intro x y
  exact ⟨fun h => by simp [h], fun h => ZFSet.ext fun z => h z⟩

lemma sat_pairing : SatS R' Axiom.pairing := by
  unfold SatS Axiom.pairing
  simp
  intro x y
  exact ⟨{y, x}, fun w => by simp [or_comm]⟩

lemma sat_union : SatS R' Axiom.union := by
  unfold SatS Axiom.union
  simp
  intro x
  exact ⟨ZFSet.sUnion x, fun z => by simp⟩

lemma sat_power : SatS R' Axiom.power := by
  unfold SatS Axiom.power
  simp [isSubsetOf]
  intro x
  refine ⟨ZFSet.powerset x, fun z => ?_⟩
  rw [ZFSet.mem_powerset]
  exact ⟨fun h w hw => h hw, fun h w hw => h w hw⟩

lemma sat_infinity : SatS R' Axiom.infinity := by
  unfold SatS Axiom.infinity
  simp [isEmpty, isSucc]
  refine ⟨ZFSet.omega, fun e he => ?_, fun x hx x' hx' => ?_⟩
  · have : e = ∅ := ZFSet.eq_empty e |>.2 he
    subst this
    exact ZFSet.omega_zero
  · have : x' = insert x x := ZFSet.ext fun z => by rw [hx' z, ZFSet.mem_insert_iff]
    subst this
    exact ZFSet.omega_succ hx

lemma sat_foundation : SatS R' Axiom.foundation := by
  unfold SatS Axiom.foundation
  simp [isNonempty]
  intro x y hy
  have hne : x ≠ ∅ := fun h => by rw [h] at hy; exact ZFSet.notMem_empty y hy
  obtain ⟨w, hw, hint⟩ := ZFSet.regularity x hne
  refine ⟨w, hw, fun z hz hzw => ?_⟩
  have : z ∈ x ∩ w := ZFSet.mem_inter.2 ⟨hz, hzw⟩
  rw [hint] at this
  exact ZFSet.notMem_empty z this

lemma sat_eq_refl : SatS R' (Theory.Eq.refl ℒₛₑₜ) := by
  unfold SatS Theory.Eq.refl
  simp

lemma sat_eq_symm : SatS R' (Theory.Eq.symm ℒₛₑₜ) := by
  unfold SatS Theory.Eq.symm
  simp

lemma sat_eq_trans : SatS R' (Theory.Eq.trans ℒₛₑₜ) := by
  unfold SatS Theory.Eq.trans
  simp

lemma sat_funcExt {k : ℕ} (f : (ℒₛₑₜ).Func k) : SatS R' (Theory.Eq.funcExt f) := (f : Empty).elim

lemma sat_relExt_eq : SatS R' (Theory.Eq.relExt (L := ℒₛₑₜ) Language.Set.Rel.eq) := by
  unfold SatS Theory.Eq.relExt
  simp [allClosure, Matrix.conj, Matrix.vecTail, Fin.addCast, Fin.addNat, Fin.castLE]

lemma sat_relExt_mem : SatS R' (Theory.Eq.relExt (L := ℒₛₑₜ) Language.Set.Rel.mem) := by
  unfold SatS Theory.Eq.relExt
  simp [allClosure, Matrix.conj, Matrix.vecTail, Fin.addCast, Fin.addNat, Fin.castLE]

lemma sat_eqAxiom : ∀ φ ∈ 𝗘𝗤 ℒₛₑₜ, SatS R' φ := by
  intro φ h
  cases h with
  | refl => exact sat_eq_refl
  | symm => exact sat_eq_symm
  | trans => exact sat_eq_trans
  | funcExt f => exact sat_funcExt f
  | relExt r =>
    cases r with
    | eq => exact sat_relExt_eq
    | mem => exact sat_relExt_mem

noncomputable def ch (X : ZFSet.{0}) : ZFSet.{0} := Classical.epsilon (fun y => y ∈ X)

lemma sat_choice : SatS R' Axiom.choice := by
  unfold SatS Axiom.choice
  simp [isNonempty, Semiformula.existsUnique]
  intro 𝓧 hne hdis
  refine ⟨ZFSet.sep (fun x => ∃ X ∈ 𝓧, x = ch X) (ZFSet.sUnion 𝓧), fun X hX => ?_⟩
  have hchX : ch X ∈ X := Classical.epsilon_spec (hne X hX)
  refine ⟨ch X, ⟨ZFSet.mem_sep.2 ⟨ZFSet.mem_sUnion.2 ⟨X, hX, hchX⟩, X, hX, rfl⟩, hchX⟩, ?_⟩
  intro z hzC hzX
  obtain ⟨_, X', hX', rfl⟩ := ZFSet.mem_sep.1 hzC
  have hX'mem : ch X' ∈ X' := Classical.epsilon_spec (hne X' hX')
  have := hdis X hX X' hX' (ch X') hzX hX'mem
  subst this
  rfl

end C14Model

namespace C14Close
open C14Sem
variable {D : Type*} (R : ∀ {k : ℕ}, (ℒₛₑₜ).Rel k → (Fin k → D) → Prop)

lemma tval_toEmpty {n : ℕ} (e : Fin n → D) (ε : ℕ → D) (ε0 : Empty → D)
    (t : Semiterm ℒₛₑₜ ℕ n) (h : t.freeVariables = ∅) :
    tval e ε0 (t.toEmpty h) = tval e ε t := by
  cases t with
  | bvar i => rfl
  | fvar x => exact absurd h (by simp [Semiterm.freeVariables])
  | func f v => exact (f : Empty).elim

lemma ev_toEmpty {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) :
    ∀ (h : φ.freeVariables = ∅) (e : Fin n → D) (ε : ℕ → D) (ε0 : Empty → D),
    ev R e ε0 (φ.toEmpty h) ↔ ev R e ε φ := by
  induction φ with
  | verum => intros; exact Iff.rfl
  | falsum => intros; exact Iff.rfl
  | rel r v =>
    intro h e ε ε0
    show R r _ ↔ R r _
    exact Iff.of_eq (congrArg _ (funext fun i => tval_toEmpty e ε ε0 (v i) _))
  | nrel r v =>
    intro h e ε ε0
    show ¬ R r _ ↔ ¬ R r _
    exact not_congr (Iff.of_eq (congrArg _ (funext fun i => tval_toEmpty e ε ε0 (v i) _)))
  | and φ ψ ih1 ih2 =>
    intro h e ε ε0
    exact and_congr (ih1 _ e ε ε0) (ih2 _ e ε ε0)
  | or φ ψ ih1 ih2 =>
    intro h e ε ε0
    exact or_congr (ih1 _ e ε ε0) (ih2 _ e ε ε0)
  | all φ ih =>
    intro h e ε ε0
    exact forall_congr' fun d => ih h _ ε ε0
  | exs φ ih =>
    intro h e ε ε0
    exact exists_congr fun d => ih h _ ε ε0

lemma ev_allClosure : ∀ {m : ℕ} (ψ : Semiformula ℒₛₑₜ ℕ m) (ε : ℕ → D),
    (∀ w : Fin m → D, ev R w ε ψ) → ev R (Fin.elim0 : Fin 0 → D) ε (∀¹* ψ)
  | 0, ψ, ε, h => h _
  | m + 1, ψ, ε, h => ev_allClosure (m := m) (∀¹ ψ) ε (fun w d => h (Matrix.vecCons d w))

lemma fixitr_fvar (n m x : ℕ) :
    Rew.fixitr n m (&x : Semiterm ℒₛₑₜ ℕ n) =
      if h : x < m then #(Fin.natAdd n ⟨x, h⟩) else &(x - m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Rew.fix (Rew.fixitr n m &x) = _
    rw [ih]
    by_cases hx : x < m
    · have hx' : x < m + 1 := by omega
      simp only [dif_pos hx, dif_pos hx']
      rfl
    · by_cases hx' : x < m + 1
      · have he : x = m := by omega
        subst x
        simp only [dif_neg (Nat.lt_irrefl m), dif_pos (Nat.lt_succ_self m), Nat.sub_self]
        rfl
      · have he : x - m = x - (m + 1) + 1 := by omega
        simp only [dif_neg hx, dif_neg hx', he]
        rfl

lemma ev_fixitr (m : ℕ) (φ : Semiproposition ℒₛₑₜ 0) (w : Fin (0 + m) → D) (ε : ℕ → D) :
    ev R w ε (Rew.fixitr 0 m ▹ φ) ↔
      ev R (Fin.elim0 : Fin 0 → D) (fun x => if h : x < m then w ⟨x, by omega⟩ else ε (x - m)) φ := by
  show ev R w ε (Semiformula.rewAux (Rew.fixitr 0 m) φ) ↔ _
  rw [ev_rew]
  have h1 : (fun x => tval w ε (Rew.fixitr 0 m (Semiterm.fvar x) : Semiterm ℒₛₑₜ ℕ (0 + m))) =
      (fun x => if h : x < m then w ⟨x, by omega⟩ else ε (x - m)) := by
    funext x
    rw [fixitr_fvar]
    by_cases hx : x < m
    · simp only [dif_pos hx, tval]
      congr 1
      exact Fin.ext (by simp)
    · simp only [dif_neg hx, tval]
  rw [h1]
  exact ev_e0 R _ _ _ _

lemma sat_univCl [Nonempty D] (φ : Proposition ℒₛₑₜ)
    (h : ∀ ε : ℕ → D, ev R (Fin.elim0 : Fin 0 → D) ε φ) :
    SatS R (Semiformula.univCl φ) := by
  unfold SatS Semiformula.univCl
  rw [ev_toEmpty R _ _ _ (fun _ => Classical.arbitrary D)]
  unfold Semiformula.univCl'
  apply ev_allClosure
  intro w
  rw [ev_fixitr]
  exact h _

end C14Close

namespace C14Model
open C14Sem C14Close

lemma sat_sep (φ : SetTheorySemiproposition 1) : SatS R' (Axiom.separationSchema φ) := by
  unfold Axiom.separationSchema
  apply sat_univCl
  intro ε
  simp
  exact fun x => ⟨_, fun z => ZFSet.mem_sep⟩

lemma sat_rep (φ : SetTheorySemiproposition 2) : SatS R' (Axiom.replacementSchema φ) := by
  unfold Axiom.replacementSchema
  apply sat_univCl
  intro ε
  have key : ∀ (a b : ZFSet.{0}) (f : Fin 2 → ZFSet.{0}), f 0 = a → f 1 = b →
      (ev R' f ε φ ↔ ev R' ![a, b] ε φ) := by
    intro a b f h0 h1
    have : f = ![a, b] := by
      funext i; refine Fin.cases h0 (fun j => ?_) i
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj; exact h1
    rw [this]
  simp only [ev_imp', ev_all', ev_exs', ev_iff', ev_bexsMem, ev_mem', ev_subst', tval_bvar,
    Semiformula.existsUnique, ev_and', ev_eq']
  intro hfun X
  have hfun' : ∀ x, ∃ y, ev R' ![x, y] ε φ ∧ ∀ z, ev R' ![x, z] ε φ → z = y := by
    intro x
    obtain ⟨y, hy, huniq⟩ := hfun x
    exact ⟨y, (key x y _ (by rfl) (by rfl)).1 hy, fun z hz => huniq z ((key x z _ (by rfl) (by rfl)).2 hz)⟩
  let F : ZFSet.{0} → ZFSet.{0} := fun x => Classical.choose (hfun' x)
  let _ : ZFSet.Definable₁ F := Classical.allZFSetDefinable _
  refine ⟨ZFSet.image F X, fun y => ?_⟩
  show y ∈ ZFSet.image F X ↔ ∃ d ∈ X, _
  rw [ZFSet.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (key x (F x) _ (by rfl) (by rfl)).2 (Classical.choose_spec (hfun' x)).1⟩
  · rintro ⟨x, hx, hP⟩
    refine ⟨x, hx, ?_⟩
    exact ((Classical.choose_spec (hfun' x)).2 y ((key x y _ (by rfl) (by rfl)).1 hP)).symm

theorem zfsetModel : ∀ ψ ∈ 𝗭𝗙𝗖, SatS R' ψ := by
  intro ψ h
  rcases h with h | h
  · cases h with
    | axiom_of_equality _ hφ => exact sat_eqAxiom _ hφ
    | axiom_of_empty_set => exact sat_empty
    | axiom_of_extentionality => exact sat_ext
    | axiom_of_pairing => exact sat_pairing
    | axiom_of_union => exact sat_union
    | axiom_of_power_set => exact sat_power
    | axiom_of_infinity => exact sat_infinity
    | axiom_of_foundation => exact sat_foundation
    | axiom_of_separation φ => exact sat_sep φ
    | axiom_of_replacement φ => exact sat_rep φ
  · have h' : ψ = Axiom.choice := h
    subst h'
    exact sat_choice

/-- In this formalization, `ZFC` does not prove `⊥` (it has the model `ZFSet`). -/
theorem zfc_consistent : 𝗭𝗙𝗖 ⊬ (⊥ : SetTheorySentence) :=
  unprovable_of_model R' zfsetModel (fun h => h)

end C14Model

namespace C14Faith
open C14Sem C14Model

/-- Von Neumann numerals in `ZFSet`. -/
noncomputable def vN : ℕ → ZFSet.{0}
  | 0 => ∅
  | k + 1 => insert (vN k) (vN k)

lemma ev_isEmpty (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε isEmpty ↔ e 0 = ∅ := by
  unfold isEmpty
  simp
  exact (ZFSet.eq_empty _).symm

lemma ev_isSucc (e : Fin 2 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε isSucc ↔ e 0 = insert (e 1) (e 1) := by
  unfold isSucc
  simp
  constructor
  · intro h; exact ZFSet.ext fun z => by rw [h z, ZFSet.mem_insert_iff]
  · intro h z; rw [h, ZFSet.mem_insert_iff]

lemma ev_numeral (k : ℕ) : ∀ (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}),
    ev R' e ε (Constant14.numeral k) ↔ e 0 = vN k := by
  induction k with
  | zero =>
    intro e ε
    show ev R' e ε (isEmpty ⇜ _) ↔ _
    rw [ev_subst', ev_isEmpty]
    rfl
  | succ k ih =>
    intro e ε
    show ev R' e ε (Semiformula.nestFormulaeFunc _ _) ↔ _
    unfold Semiformula.nestFormulaeFunc
    simp only [allItr, ev_all', ev_imp', Matrix.conj, ev_and', ev_top', and_true, ev_subst']
    constructor
    · intro h
      have := h (vN k) ((ih _ ε).2 rfl)
      rw [ev_isSucc] at this
      exact this
    · intro h x hx
      have hx' : x = vN k := (ih _ ε).1 hx
      subst hx'
      rw [ev_isSucc]
      exact h

lemma ev_doubleton (e : Fin 3 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε doubleton.dfn ↔ e 0 = {e 1, e 2} := by
  unfold doubleton.dfn
  simp
  constructor
  · intro h; exact ZFSet.ext fun z => by rw [h z]; simp
  · intro h z; rw [h]; simp

lemma ev_singleton (e : Fin 2 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε singleton.dfn ↔ e 0 = {e 1, e 1} := by
  unfold singleton.dfn
  rw [ev_subst', ev_doubleton]
  exact Iff.rfl

lemma ev_kpair (e : Fin 3 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε kpair.dfn ↔ e 0 = {{e 1, e 1}, {e 1, e 2}} := by
  unfold kpair.dfn
  simp only [ev_all', ev_imp', ev_subst', ev_singleton, ev_doubleton]
  show (∀ x', x' = {e 1, e 1} → ∀ z, z = {e 1, e 2} → e 0 = {x', z}) ↔ _
  constructor
  · intro h; exact h _ rfl _ rfl
  · intro h x' hx' z hz; subst hx' hz; exact h

lemma ev_sUnion (e : Fin 2 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε sUnion.dfn ↔ e 0 = ZFSet.sUnion (e 1) := by
  unfold sUnion.dfn
  simp
  constructor
  · intro h; exact ZFSet.ext fun z => by rw [h z, ZFSet.mem_sUnion]
  · intro h z; rw [h, ZFSet.mem_sUnion]

lemma ev_union (e : Fin 3 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε union.dfn ↔ e 0 = ZFSet.sUnion {e 1, e 2} := by
  unfold union.dfn
  simp only [ev_all', ev_imp', ev_subst', ev_doubleton, ev_sUnion]
  show (∀ d, d = {e 1, e 2} → e 0 = ZFSet.sUnion d) ↔ _
  exact ⟨fun h => h _ rfl, fun h d hd => hd ▸ h⟩

lemma ev_insert (e : Fin 3 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε insert.dfn ↔ e 0 = ZFSet.sUnion {{e 1, e 1}, e 2} := by
  unfold insert.dfn
  simp only [ev_all', ev_imp', ev_subst', ev_singleton, ev_union]
  show (∀ s, s = {e 1, e 1} → e 0 = ZFSet.sUnion {s, e 2}) ↔ _
  exact ⟨fun h => h _ rfl, fun h s hs => hs ▸ h⟩

lemma ev_prod (e : Fin 3 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε prod.dfn ↔
      ∀ z, z ∈ e 0 ↔ ∃ x ∈ e 1, ∃ y ∈ e 2, z = {{x, x}, {x, y}} := by
  unfold prod.dfn
  simp only [ev_all', ev_iff', ev_mem', ev_bexsMem, ev_subst', ev_kpair, tval_bvar]
  exact Iff.rfl

lemma ev_sInter (e : Fin 2 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε sInter.dfn ↔ ∀ z, z ∈ e 0 ↔ (∃ y, y ∈ e 1) ∧ ∀ y ∈ e 1, z ∈ y := by
  unfold sInter.dfn isNonempty
  simp only [ev_all', ev_iff', ev_mem', ev_and', ev_exs', ev_ballMem, ev_subst', tval_bvar]
  exact Iff.rfl

lemma pair_inter_char (a b z : ZFSet.{0}) :
    (z ∈ ({a, a} : ZFSet.{0}) ↔ (∃ y, y ∈ ({{a, a}, {a, b}} : ZFSet.{0})) ∧
      ∀ y ∈ ({{a, a}, {a, b}} : ZFSet.{0}), z ∈ y) := by
  constructor
  · intro hz
    have hza : z = a := by simpa using hz
    subst hza
    refine ⟨⟨{z, z}, by simp⟩, fun y hy => ?_⟩
    rcases ZFSet.mem_insert_iff.1 hy with rfl | hy
    · simp
    · rw [ZFSet.mem_singleton] at hy; subst hy; simp
  · rintro ⟨_, h⟩
    exact h _ (by simp)

lemma ev_pi1_pair (a b p : ZFSet.{0}) (e : Fin 2 → ZFSet.{0}) (he0 : e 0 = p)
    (he1 : e 1 = {{a, a}, {a, b}}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε kpair.π₁.dfn ↔ p = a := by
  unfold kpair.π₁.dfn
  simp only [ev_all', ev_imp', ev_subst', ev_sInter, ev_sUnion]
  show (∀ i, (∀ z, z ∈ i ↔ (∃ y, y ∈ e 1) ∧ ∀ y ∈ e 1, z ∈ y) → e 0 = ZFSet.sUnion i) ↔ _
  rw [he0, he1]
  have hi : ∀ i : ZFSet.{0}, (∀ z, z ∈ i ↔ (∃ y, y ∈ ({{a, a}, {a, b}} : ZFSet.{0})) ∧
      ∀ y ∈ ({{a, a}, {a, b}} : ZFSet.{0}), z ∈ y) ↔ i = {a, a} := by
    intro i
    constructor
    · intro h; exact ZFSet.ext fun z => by rw [h z, pair_inter_char]
    · intro h z; rw [h, pair_inter_char]
  simp only [hi]
  have hu : ZFSet.sUnion ({a, a} : ZFSet.{0}) = a := by
    ext z; simp
  constructor
  · intro h; rw [h _ rfl, hu]
  · intro h i hi'; rw [hi', hu, h]

lemma ev_pi2_pair (a b p : ZFSet.{0}) (e : Fin 2 → ZFSet.{0}) (he0 : e 0 = p)
    (he1 : e 1 = {{a, a}, {a, b}}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε kpair.π₂.dfn ↔ p = b := by
  unfold kpair.π₂.dfn
  simp only [ev_all', ev_imp', ev_subst', ev_sInter, ev_sUnion, ev_iff', ev_mem', ev_and', ev_eq',
    tval_bvar]
  show (∀ u, u = ZFSet.sUnion (e 1) → ∀ i, (∀ z, z ∈ i ↔ (∃ y, y ∈ e 1) ∧ ∀ y ∈ e 1, z ∈ y) →
      ∀ s, (∀ z, z ∈ s ↔ z ∈ u ∧ (z ∈ i → u = i)) → e 0 = ZFSet.sUnion s) ↔ _
  rw [he0, he1]
  set U : ZFSet.{0} := ZFSet.sUnion {{a, a}, {a, b}} with hUdef
  have hU : ∀ z, z ∈ U ↔ z = a ∨ z = b := by
    intro z
    rw [hUdef, ZFSet.mem_sUnion]
    constructor
    · rintro ⟨w, hw, hzw⟩
      rcases ZFSet.mem_insert_iff.1 hw with rfl | hw
      · left; simpa using hzw
      · rw [ZFSet.mem_singleton] at hw; subst hw; simpa using hzw
    · rintro (rfl | rfl)
      · exact ⟨{z, z}, by simp, by simp⟩
      · exact ⟨{a, z}, by simp, by simp⟩
  have hi : ∀ i : ZFSet.{0}, (∀ z, z ∈ i ↔ (∃ y, y ∈ ({{a, a}, {a, b}} : ZFSet.{0})) ∧
      ∀ y ∈ ({{a, a}, {a, b}} : ZFSet.{0}), z ∈ y) ↔ i = {a, a} := by
    intro i
    constructor
    · intro h; exact ZFSet.ext fun z => by rw [h z, pair_inter_char]
    · intro h z; rw [h, pair_inter_char]
  have hUI : U = {a, a} ↔ b = a := by
    constructor
    · intro h
      have : b ∈ U := (hU b).2 (Or.inr rfl)
      rw [h] at this; simpa using this
    · intro h; subst h
      exact ZFSet.ext fun z => by rw [hU]; simp
  have hs : ∀ z, z ∈ ({b, b} : ZFSet.{0}) ↔ z ∈ U ∧ (z ∈ ({a, a} : ZFSet.{0}) → U = {a, a}) := by
    intro z
    rw [hU, hUI]
    simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton, or_self]
    constructor
    · rintro rfl; exact ⟨Or.inr rfl, fun h => h.symm ▸ rfl⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact h1.trans (h2 h1).symm
      · exact h1
  have hu : ZFSet.sUnion ({b, b} : ZFSet.{0}) = b := by
    ext z; simp
  constructor
  · intro h
    have := h U rfl {a, a} ((hi _).2 rfl) {b, b} hs
    rw [this, hu]
  · intro hp u hu' i hi' s hs'
    rw [(hi i).1 hi'] at hs'
    subst hu'
    have hseq : s = {b, b} := ZFSet.ext fun z => by rw [hs' z, hs z]
    rw [hseq, hu, hp]

lemma mk_ofNat (n : ℕ) : ZFSet.mk (PSet.ofNat n) = vN n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show insert (ZFSet.mk (PSet.ofNat n)) (ZFSet.mk (PSet.ofNat n)) = _
    rw [ih]
    rfl

lemma vN_mem_omega (n : ℕ) : vN n ∈ ZFSet.omega.{0} := by
  induction n with
  | zero => exact ZFSet.omega_zero
  | succ n ih => exact ZFSet.omega_succ ih

lemma mem_omega_iff (x : ZFSet.{0}) : x ∈ ZFSet.omega ↔ ∃ n, x = vN n := by
  constructor
  · induction x using Quotient.inductionOn with
    | h p =>
      intro h
      rw [ZFSet.mk_eq] at h ⊢
      have h' : p ∈ PSet.omega := ZFSet.mk_mem_iff.1 h
      obtain ⟨b, hb⟩ := PSet.mem_def.1 h'
      exact ⟨b.down, by rw [← mk_ofNat]; exact ZFSet.sound hb⟩
  · rintro ⟨n, rfl⟩
    exact vN_mem_omega n

/-- `ZFSet.omega` is the least inductive set. -/
lemma mem_omega_iff_inductive (x : ZFSet.{0}) :
    x ∈ ZFSet.omega ↔ ∀ I : ZFSet.{0}, (∅ ∈ I ∧ ∀ y ∈ I, insert y y ∈ I) → x ∈ I := by
  constructor
  · intro hx I hI
    obtain ⟨n, rfl⟩ := (mem_omega_iff x).1 hx
    induction n with
    | zero => exact hI.1
    | succ n ih => exact hI.2 _ (ih (vN_mem_omega n))
  · intro h
    exact h _ ⟨ZFSet.omega_zero, fun y hy => ZFSet.omega_succ hy⟩

lemma ev_IsInductive (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε IsInductive.dfn ↔ (∅ ∈ e 0 ∧ ∀ y ∈ e 0, insert y y ∈ e 0) := by
  unfold IsInductive.dfn
  simp only [ev_and', ev_all', ev_imp', ev_subst', ev_isEmpty, ev_ballMem, ev_isSucc, ev_mem', tval_bvar]
  show ((∀ x, x = ∅ → x ∈ e 0) ∧ ∀ y ∈ e 0, ∀ y', y' = insert y y → y' ∈ e 0) ↔ _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1 _ rfl, fun y hy => h2 y hy _ rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun x hx => hx ▸ h1, fun y hy y' hy' => hy' ▸ h2 y hy⟩

lemma ev_isω (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε isω ↔ e 0 = ZFSet.omega := by
  unfold isω
  simp only [ev_all', ev_iff', ev_imp', ev_mem', ev_subst', ev_IsInductive, tval_bvar]
  show (∀ x, x ∈ e 0 ↔ ∀ I, (∅ ∈ I ∧ ∀ y ∈ I, insert y y ∈ I) → x ∈ I) ↔ _
  constructor
  · intro h; exact ZFSet.ext fun x => by rw [h x, mem_omega_iff_inductive]
  · intro h x; rw [h, mem_omega_iff_inductive]

lemma ev_range (e : Fin 2 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε range.dfn ↔ ∀ y, y ∈ e 0 ↔ ∃ x, ({{x, x}, {x, y}} : ZFSet.{0}) ∈ e 1 := by
  unfold range.dfn
  simp only [ev_all', ev_iff', ev_imp', ev_exs', ev_eq', ev_mem', ev_subst', tval_bvar,
    Semiformula.nestFormulaeFunc, allItr, Matrix.conj, ev_and', ev_top', and_true, ev_kpair,
    Matrix.cons_val_zero, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ]
  show (∀ y, (∀ x1, x1 = y → ∀ x2, x2 = e 0 → x1 ∈ x2) ↔
      ∃ x, ∀ x1, (∀ b a, a = x ∧ b = y → x1 = {{a, a}, {a, b}}) → ∀ x2, x2 = e 1 → x1 ∈ x2) ↔ _
  simp


noncomputable def rng (f : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.sep (fun y => ∃ x, ({{x, x}, {x, y}} : ZFSet.{0}) ∈ f) (ZFSet.sUnion (ZFSet.sUnion f))

lemma mem_rng (f y : ZFSet.{0}) : y ∈ rng f ↔ ∃ x, ({{x, x}, {x, y}} : ZFSet.{0}) ∈ f := by
  unfold rng
  rw [ZFSet.mem_sep]
  constructor
  · exact fun h => h.2
  · rintro ⟨x, hx⟩
    refine ⟨?_, x, hx⟩
    rw [ZFSet.mem_sUnion]
    refine ⟨{x, y}, ?_, by simp⟩
    rw [ZFSet.mem_sUnion]
    exact ⟨_, hx, by simp⟩

lemma ev_value (e : Fin 3 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε value.dfn ↔ ∀ z, z ∈ e 0 ↔
      z ∈ ZFSet.sUnion (rng (e 1)) ∧ ∃ y, z ∈ y ∧ ({{e 2, e 2}, {e 2, y}} : ZFSet.{0}) ∈ e 1 := by
  unfold value.dfn
  simp only [ev_all', ev_iff', ev_imp', ev_exs', ev_eq', ev_mem', ev_subst', tval_bvar,
    Semiformula.nestFormulaeFunc, allItr, Matrix.conj, ev_and', ev_top', and_true, ev_kpair,
    Matrix.cons_val_zero, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ, ev_range, ev_sUnion]
  show (∀ z, (∀ d1, d1 = z → ∀ d2, d2 = e 0 → d1 ∈ d2) ↔
      (∀ d1, d1 = z → ∀ U, (∀ r, (∀ f', f' = e 1 → ∀ y, y ∈ r ↔ ∃ x', ({{x', x'}, {x', y}} : ZFSet.{0}) ∈ f') →
          U = ZFSet.sUnion r) → d1 ∈ U) ∧
      ∃ y, (∀ d2, d2 = z → ∀ d3, d3 = y → d2 ∈ d3) ∧
        ∀ p, (∀ b a, a = e 2 ∧ b = y → p = {{a, a}, {a, b}}) → ∀ F, F = e 1 → p ∈ F) ↔ _
  have hr : ∀ U : ZFSet.{0}, (∀ r, (∀ f', f' = e 1 → ∀ y, y ∈ r ↔ ∃ x', ({{x', x'}, {x', y}} : ZFSet.{0}) ∈ f') →
      U = ZFSet.sUnion r) ↔ U = ZFSet.sUnion (rng (e 1)) := by
    intro U
    constructor
    · intro h; exact h _ (fun f' hf' y => by rw [hf', mem_rng])
    · intro h r hr'
      have : r = rng (e 1) := ZFSet.ext fun y => by rw [hr' _ rfl y, mem_rng]
      rw [h, this]
  simp only [hr]
  simp


lemma ev_function (e : Fin 3 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε function.dfn ↔ ∀ f, f ∈ e 0 ↔
      (∀ P : ZFSet.{0}, (∀ z : ZFSet.{0}, z ∈ P ↔ ∃ x ∈ e 2, ∃ y ∈ e 1, z = ({{x, x}, {x, y}} : ZFSet.{0})) →
        ∀ w ∈ f, w ∈ P) ∧
      ∀ x ∈ e 2, ∃ y, ({{x, x}, {x, y}} : ZFSet.{0}) ∈ f ∧
        ∀ z, ({{x, x}, {x, z}} : ZFSet.{0}) ∈ f → z = y := by
  unfold function.dfn
  simp only [ev_all', ev_iff', ev_imp', ev_exs', ev_eq', ev_mem', ev_subst', tval_bvar,
    Semiformula.nestFormulaeFunc, Semiformula.nestFormulae, allItr, Matrix.conj, ev_and', ev_top',
    and_true, ev_kpair, Matrix.cons_val_zero, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ,
    ev_prod, ev_ballMem, Semiformula.existsUnique, isSubsetOf]
  show (∀ f : ZFSet.{0}, (∀ d1 : ZFSet.{0}, d1 = f → ∀ d2 : ZFSet.{0}, d2 = e 0 → d1 ∈ d2) ↔
      (∀ d1 d2 : ZFSet.{0}, (d2 = f ∧ ∀ d3 d4 : ZFSet.{0}, (d4 = e 2 ∧ d3 = e 1) →
          ∀ z : ZFSet.{0}, z ∈ d1 ↔ ∃ x ∈ d4, ∃ y ∈ d3, z = ({{x, x}, {x, y}} : ZFSet.{0})) →
          ∀ w ∈ d2, w ∈ d1) ∧
      ∀ X' : ZFSet.{0}, X' = e 2 → ∀ x ∈ X', ∃ y : ZFSet.{0},
        (∀ p : ZFSet.{0}, (∀ b a : ZFSet.{0}, (a = x ∧ b = y) → p = ({{a, a}, {a, b}} : ZFSet.{0})) →
          ∀ F' : ZFSet.{0}, F' = f → p ∈ F') ∧
        ∀ z : ZFSet.{0}, (∀ p : ZFSet.{0}, (∀ b a : ZFSet.{0}, (a = x ∧ b = z) →
          p = ({{a, a}, {a, b}} : ZFSet.{0})) → ∀ F' : ZFSet.{0}, F' = f → p ∈ F') → z = y) ↔ _
  simp


/-- `F` is the set of all functions from `X` to `Y` (pairs encoded as in the upstream file). -/
def FunSet (F Y X : ZFSet.{0}) : Prop :=
  ∀ g, g ∈ F ↔ (∀ P : ZFSet.{0}, (∀ z : ZFSet.{0}, z ∈ P ↔ ∃ x ∈ X, ∃ y ∈ Y,
      z = ({{x, x}, {x, y}} : ZFSet.{0})) → ∀ w ∈ g, w ∈ P) ∧
    ∀ x ∈ X, ∃ y, ({{x, x}, {x, y}} : ZFSet.{0}) ∈ g ∧ ∀ z, ({{x, x}, {x, z}} : ZFSet.{0}) ∈ g → z = y

lemma ev_IsFunction (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε IsFunction.dfn ↔ ∃ X Y : ZFSet.{0}, ∀ F, FunSet F Y X → e 0 ∈ F := by
  unfold IsFunction.dfn
  simp only [ev_exs', ev_all', ev_imp', ev_mem', ev_eq', ev_subst', tval_bvar,
    Semiformula.nestFormulaeFunc, allItr, Matrix.conj, ev_and', ev_top', and_true,
    Matrix.cons_val_zero, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ, ev_function]
  show (∃ X Y : ZFSet.{0}, ∀ x1 : ZFSet.{0}, x1 = e 0 → ∀ x2 : ZFSet.{0},
      (∀ b a : ZFSet.{0}, (a = Y ∧ b = X) → FunSet x2 a b) → x1 ∈ x2) ↔ _
  constructor
  · rintro ⟨X, Y, h⟩
    exact ⟨X, Y, fun F hF => h _ rfl F (fun b a hab => by
      obtain ⟨ha, hb⟩ := hab; subst ha; subst hb; exact hF)⟩
  · rintro ⟨X, Y, h⟩
    exact ⟨X, Y, fun x1 hx1 x2 hx2 => hx1 ▸ h x2 (hx2 X Y ⟨rfl, rfl⟩)⟩

/-- `v` is the value of `f` at `y`, as defined upstream. -/
def Val (v f y : ZFSet.{0}) : Prop :=
  ∀ z, z ∈ v ↔ z ∈ ZFSet.sUnion (rng f) ∧ ∃ u, z ∈ u ∧ ({{y, y}, {y, u}} : ZFSet.{0}) ∈ f

lemma ev_orbit (e : Fin 3 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε Constant14.orbit ↔ (∃ X Y : ZFSet.{0}, ∀ F, FunSet F Y X → e 1 ∈ F) ∧
      ∀ z, z ∈ e 0 ↔ ∀ A : ZFSet.{0}, (e 2 ∈ A ∧ ∀ y ∈ A, ∀ v, Val v (e 1) y → v ∈ A) → z ∈ A := by
  unfold Constant14.orbit
  simp only [ev_exs', ev_all', ev_imp', ev_mem', ev_eq', ev_subst', tval_bvar, ev_iff',
    Semiformula.nestFormulaeFunc, Semiformula.nestFormulae, allItr, Matrix.conj, ev_and', ev_top',
    and_true, Matrix.cons_val_zero, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ,
    ev_IsFunction, ev_value, ev_ballMem]
  show ((∀ a : ZFSet.{0}, a = e 1 → ∃ X Y : ZFSet.{0}, ∀ F, FunSet F Y X → a ∈ F) ∧
      ∀ z : ZFSet.{0}, (∀ x1 : ZFSet.{0}, x1 = z → ∀ x2 : ZFSet.{0}, x2 = e 0 → x1 ∈ x2) ↔
        ∀ A : ZFSet.{0}, ((∀ x1 : ZFSet.{0}, x1 = e 2 → ∀ x2 : ZFSet.{0}, x2 = A → x1 ∈ x2) ∧
          ∀ vt : ZFSet.{0}, vt = A → ∀ y ∈ vt, ∀ x1 : ZFSet.{0},
            (∀ b a : ZFSet.{0}, (a = e 1 ∧ b = y) → Val x1 a b) → ∀ x2 : ZFSet.{0}, x2 = A → x1 ∈ x2) →
          ∀ x1 : ZFSet.{0}, x1 = z → ∀ x2 : ZFSet.{0}, x2 = A → x1 ∈ x2) ↔ _
  simp only [forall_eq, forall_eq', and_imp, forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂]


lemma ev_integers (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε Constant14.integers ↔ ∀ P : ZFSet.{0},
      (∀ z : ZFSet.{0}, z ∈ P ↔ ∃ x ∈ vN 2, ∃ y ∈ ZFSet.omega.{0}, z = ({{x, x}, {x, y}} : ZFSet.{0})) →
      e 0 = P := by
  unfold Constant14.integers
  simp only [ev_exs', ev_all', ev_imp', ev_mem', ev_eq', ev_subst', tval_bvar, ev_iff',
    Semiformula.nestFormulaeFunc, Semiformula.nestFormulae, allItr, Matrix.conj, ev_and', ev_top',
    and_true, true_implies, Matrix.cons_val_zero, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, ev_prod, ev_numeral, ev_isω]
  show (∀ x1 : ZFSet.{0}, x1 = e 0 → ∀ x2 : ZFSet.{0}, (∀ b a : ZFSet.{0}, (a = vN 2 ∧ b = ZFSet.omega) →
      ∀ z : ZFSet.{0}, z ∈ x2 ↔ ∃ x ∈ a, ∃ y ∈ b, z = ({{x, x}, {x, y}} : ZFSet.{0})) → x1 = x2) ↔ _
  simp only [forall_eq, forall_eq', and_imp, forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂]


lemma ev_integerZero (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε Constant14.integerZero ↔ e 0 = ({{vN 0, vN 0}, {vN 0, vN 0}} : ZFSet.{0}) := by
  unfold Constant14.integerZero
  simp only [ev_exs', ev_all', ev_imp', ev_mem', ev_eq', ev_subst', tval_bvar, ev_iff',
    Semiformula.nestFormulaeFunc, Semiformula.nestFormulae, allItr, Matrix.conj, ev_and', ev_top',
    and_true, true_implies, Matrix.cons_val_zero, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, ev_kpair, ev_numeral]
  show (∀ x1 : ZFSet.{0}, x1 = e 0 → ∀ x2 : ZFSet.{0}, (∀ b a : ZFSet.{0}, (a = vN 0 ∧ b = vN 0) →
      x2 = ({{a, a}, {a, b}} : ZFSet.{0})) → x1 = x2) ↔ _
  simp only [forall_eq, forall_eq', and_imp, forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂]


/-- The Cartesian product, with pairs encoded as upstream. -/
noncomputable def prodSet (X Y : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.sep (fun z => ∃ x ∈ X, ∃ y ∈ Y, z = ({{x, x}, {x, y}} : ZFSet.{0}))
    (ZFSet.powerset (ZFSet.powerset (X ∪ Y)))

lemma mem_prodSet (X Y z : ZFSet.{0}) :
    z ∈ prodSet X Y ↔ ∃ x ∈ X, ∃ y ∈ Y, z = ({{x, x}, {x, y}} : ZFSet.{0}) := by
  unfold prodSet
  rw [ZFSet.mem_sep]
  constructor
  · exact fun h => h.2
  · rintro ⟨x, hx, y, hy, rfl⟩
    refine ⟨?_, x, hx, y, hy, rfl⟩
    rw [ZFSet.mem_powerset]
    intro w hw
    rw [ZFSet.mem_powerset]
    intro u hu
    rw [ZFSet.mem_union]
    simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton] at hw
    rcases hw with rfl | rfl
    · simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton, or_self] at hu
      subst hu; exact Or.inl hx
    · simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hy

lemma eq_prodSet_iff (Z X Y : ZFSet.{0}) :
    (∀ P : ZFSet.{0}, (∀ z : ZFSet.{0}, z ∈ P ↔ ∃ x ∈ X, ∃ y ∈ Y,
      z = ({{x, x}, {x, y}} : ZFSet.{0})) → Z = P) ↔ Z = prodSet X Y := by
  constructor
  · intro h; exact h _ (mem_prodSet X Y)
  · intro h P hP; rw [h]; exact ZFSet.ext fun z => by rw [mem_prodSet, hP]

lemma ev_integers' (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε Constant14.integers ↔ e 0 = prodSet (vN 2) ZFSet.omega := by
  rw [ev_integers, eq_prodSet_iff]


lemma subset_prod_iff (X Y g : ZFSet.{0}) :
    (∀ P : ZFSet.{0}, (∀ z : ZFSet.{0}, z ∈ P ↔ ∃ x ∈ X, ∃ y ∈ Y,
      z = ({{x, x}, {x, y}} : ZFSet.{0})) → ∀ w ∈ g, w ∈ P) ↔ ∀ w ∈ g, w ∈ prodSet X Y := by
  constructor
  · intro h; exact h _ (mem_prodSet X Y)
  · intro h P hP w hw
    have : P = prodSet X Y := ZFSet.ext fun z => by rw [hP, mem_prodSet]
    rw [this]; exact h w hw

/-- The set of all functions from `X` to `Y`, pairs encoded as upstream. -/
noncomputable def funSet (X Y : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.sep (fun g => (∀ w ∈ g, w ∈ prodSet X Y) ∧ ∀ x ∈ X, ∃ y, ({{x, x}, {x, y}} : ZFSet.{0}) ∈ g ∧
    ∀ z, ({{x, x}, {x, z}} : ZFSet.{0}) ∈ g → z = y) (ZFSet.powerset (prodSet X Y))

lemma mem_funSet (X Y g : ZFSet.{0}) :
    g ∈ funSet X Y ↔ (∀ w ∈ g, w ∈ prodSet X Y) ∧ ∀ x ∈ X, ∃ y, ({{x, x}, {x, y}} : ZFSet.{0}) ∈ g ∧
      ∀ z, ({{x, x}, {x, z}} : ZFSet.{0}) ∈ g → z = y := by
  unfold funSet
  rw [ZFSet.mem_sep]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [ZFSet.mem_powerset]
    intro w hw
    exact h.1 w hw

lemma FunSet_iff (F Y X : ZFSet.{0}) : FunSet F Y X ↔ F = funSet X Y := by
  unfold FunSet
  simp only [subset_prod_iff]
  constructor
  · intro h; exact ZFSet.ext fun g => by rw [h g, mem_funSet]
  · intro h g; rw [h, mem_funSet]


lemma prodChar_iff (B X Y : ZFSet.{0}) :
    (∀ z : ZFSet.{0}, z ∈ B ↔ ∃ x ∈ X, ∃ y ∈ Y, z = ({{x, x}, {x, y}} : ZFSet.{0})) ↔
      B = prodSet X Y := by
  constructor
  · intro h; exact ZFSet.ext fun z => by rw [h z, mem_prodSet]
  · intro h z; rw [h, mem_prodSet]

lemma ev_configSet (n : ℕ) (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε (Constant14.configSet n) ↔ e 0 = prodSet (vN n)
      (prodSet (prodSet (vN 2) ZFSet.omega) (funSet (prodSet (vN 2) ZFSet.omega) (vN 2))) := by
  unfold Constant14.configSet
  simp only [ev_exs', ev_all', ev_imp', ev_mem', ev_eq', ev_subst', tval_bvar, ev_iff',
    Semiformula.nestFormulaeFunc, Semiformula.nestFormulae, allItr, Matrix.conj, ev_and', ev_top',
    and_true, true_implies, Matrix.cons_val_zero, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, ev_prod, ev_numeral, ev_integers', ev_function]
  show (∀ x1 : ZFSet.{0}, x1 = e 0 → ∀ x2 : ZFSet.{0},
      (∀ b a : ZFSet.{0}, (a = vN n ∧ ∀ b' a' : ZFSet.{0}, (a' = prodSet (vN 2) ZFSet.omega ∧
          ∀ b'' a'' : ZFSet.{0}, (a'' = vN 2 ∧ b'' = prodSet (vN 2) ZFSet.omega) → FunSet b' a'' b'') →
          ∀ z : ZFSet.{0}, z ∈ b ↔ ∃ x ∈ a', ∃ y ∈ b', z = ({{x, x}, {x, y}} : ZFSet.{0})) →
        ∀ z : ZFSet.{0}, z ∈ x2 ↔ ∃ x ∈ a, ∃ y ∈ b, z = ({{x, x}, {x, y}} : ZFSet.{0})) → x1 = x2) ↔ _
  simp only [FunSet_iff, prodChar_iff, forall_eq, forall_eq', and_imp, forall_apply_eq_imp_iff,
    forall_apply_eq_imp_iff₂]


/-- `ψ` defines the set `A` in `ZFSet`. -/
def Defines (ψ : SetTheorySemisentence 1) (A : ZFSet.{0}) : Prop :=
  ∀ (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}), ev R' e ε ψ ↔ e 0 = A

lemma defines_zero : Defines Constant14.zero ∅ := by
  intro e ε
  show ev R' e ε (isEmpty ⇜ _) ↔ _
  rw [ev_subst', ev_isEmpty]
  exact Iff.rfl

lemma defines_numeral (k : ℕ) : Defines (Constant14.numeral k) (vN k) := fun e ε => ev_numeral k e ε

lemma defines_finiteSet_cons {x : SetTheorySemisentence 1} {xs : List (SetTheorySemisentence 1)}
    {A B : ZFSet.{0}} (hx : Defines x A) (hs : Defines (Constant14.finiteSet xs) B) :
    Defines (Constant14.finiteSet (x :: xs)) (ZFSet.sUnion {{A, A}, B}) := by
  have hx' : ∀ e ε, ev R' e ε x ↔ e 0 = A := hx
  have hs' : ∀ e ε, ev R' e ε (Constant14.finiteSet xs) ↔ e 0 = B := hs
  intro e ε
  show ev R' e ε (Semiformula.nestFormulaeFunc _ _) ↔ _
  unfold Semiformula.nestFormulaeFunc
  simp only [ev_all', ev_imp', ev_subst', allItr, Matrix.conj, ev_and', ev_top', and_true,
    Matrix.cons_val_zero, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ, hx', hs', ev_insert]
  show (∀ b a : ZFSet.{0}, (a = A ∧ b = B) → e 0 = ZFSet.sUnion {{a, a}, b}) ↔ _
  simp only [forall_eq, forall_eq', and_imp, forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂]

lemma defines_setPair {x y : SetTheorySemisentence 1} {A B : ZFSet.{0}}
    (hx : Defines x A) (hy : Defines y B) :
    Defines (Constant14.setPair x y) ({{A, A}, {A, B}} : ZFSet.{0}) := by
  have hx' : ∀ e ε, ev R' e ε x ↔ e 0 = A := hx
  have hy' : ∀ e ε, ev R' e ε y ↔ e 0 = B := hy
  intro e ε
  show ev R' e ε (Semiformula.nestFormulaeFunc _ _) ↔ _
  unfold Semiformula.nestFormulaeFunc
  simp only [ev_all', ev_imp', ev_subst', allItr, Matrix.conj, ev_and', ev_top', and_true,
    Matrix.cons_val_zero, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ, hx', hy', ev_kpair]
  show (∀ b a : ZFSet.{0}, (a = A ∧ b = B) → e 0 = ({{a, a}, {a, b}} : ZFSet.{0})) ↔ _
  simp only [forall_eq, forall_eq', and_imp, forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂]


lemma defines_setTriple {x y z : SetTheorySemisentence 1} {A B C : ZFSet.{0}}
    (hx : Defines x A) (hy : Defines y B) (hz : Defines z C) :
    Defines (Constant14.setTriple x y z)
      ({{A, A}, {A, ({{B, B}, {B, C}} : ZFSet.{0})}} : ZFSet.{0}) :=
  defines_setPair hx (defines_setPair hy hz)

lemma defines_transitionEntry (q s q' w d : ℕ) :
    Defines (Constant14.transitionEntry q s q' w d)
      (let P : ZFSet.{0} := {{vN q, vN q}, {vN q, vN s}}
       let T : ZFSet.{0} := {{vN q', vN q'}, {vN q', ({{vN w, vN w}, {vN w, vN d}} : ZFSet.{0})}}
       ({{P, P}, {P, T}} : ZFSet.{0})) :=
  defines_setPair (defines_setPair (defines_numeral q) (defines_numeral s))
    (defines_setTriple (defines_numeral q') (defines_numeral w) (defines_numeral d))

lemma defines_finiteSet {l : List (SetTheorySemisentence 1)} {vals : List ZFSet.{0}}
    (h : List.Forall₂ Defines l vals) :
    Defines (Constant14.finiteSet l) (vals.foldr (fun A B => ZFSet.sUnion {{A, A}, B}) ∅) := by
  induction h with
  | nil => exact defines_zero
  | cons hx _ ih => exact defines_finiteSet_cons hx ih


lemma ev_emptyTape (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε Constant14.emptyTape ↔
      e 0 ∈ funSet (prodSet (vN 2) ZFSet.omega) (vN 2) ∧
      ∀ i ∈ prodSet (vN 2) ZFSet.omega, ∀ v : ZFSet.{0}, Val v (e 0) i → v = vN 0 := by
  unfold Constant14.emptyTape
  simp only [ev_exs', ev_all', ev_imp', ev_mem', ev_eq', ev_subst', tval_bvar, ev_iff',
    Semiformula.nestFormulaeFunc, Semiformula.nestFormulae, allItr, Matrix.conj, ev_and', ev_top',
    and_true, true_implies, Matrix.cons_val_zero, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, ev_numeral, ev_integers', ev_function, ev_value, ev_ballMem]
  show ((∀ x1 : ZFSet.{0}, x1 = e 0 → ∀ x2 : ZFSet.{0},
      (∀ b a : ZFSet.{0}, (a = vN 2 ∧ b = prodSet (vN 2) ZFSet.omega) → FunSet x2 a b) → x1 ∈ x2) ∧
    ∀ vt : ZFSet.{0}, vt = prodSet (vN 2) ZFSet.omega → ∀ i ∈ vt, ∀ x1 : ZFSet.{0},
      (∀ b a : ZFSet.{0}, (a = e 0 ∧ b = i) → Val x1 a b) → ∀ x2 : ZFSet.{0}, x2 = vN 0 → x1 = x2) ↔ _
  simp only [FunSet_iff, forall_eq, forall_eq', and_imp, forall_apply_eq_imp_iff,
    forall_apply_eq_imp_iff₂]


/-- The `ZFSet` meaning of the upstream `emptyTape` formula. -/
def ETape (t : ZFSet.{0}) : Prop :=
  t ∈ funSet (prodSet (vN 2) ZFSet.omega) (vN 2) ∧
    ∀ i ∈ prodSet (vN 2) ZFSet.omega, ∀ v : ZFSet.{0}, Val v t i → v = vN 0

lemma ev_initialConfig (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε Constant14.initialConfig ↔ ∀ x2 : ZFSet.{0},
      (∀ b : ZFSet.{0}, (∀ b' : ZFSet.{0}, ETape b' →
          b = ({{({{vN 0, vN 0}, {vN 0, vN 0}} : ZFSet.{0}), {{vN 0, vN 0}, {vN 0, vN 0}}},
            {({{vN 0, vN 0}, {vN 0, vN 0}} : ZFSet.{0}), b'}} : ZFSet.{0})) →
        x2 = ({{vN 0, vN 0}, {vN 0, b}} : ZFSet.{0})) → e 0 = x2 := by
  unfold Constant14.initialConfig
  simp only [ev_exs', ev_all', ev_imp', ev_mem', ev_eq', ev_subst', tval_bvar, ev_iff',
    Semiformula.nestFormulaeFunc, Semiformula.nestFormulae, allItr, Matrix.conj, ev_and', ev_top',
    and_true, true_implies, Matrix.cons_val_zero, Matrix.vecTail, Function.comp_apply,
    Matrix.cons_val_succ, ev_numeral, ev_kpair, ev_integerZero, ev_emptyTape]
  show (∀ x1 : ZFSet.{0}, x1 = e 0 → ∀ x2 : ZFSet.{0},
      (∀ b a : ZFSet.{0}, (a = vN 0 ∧ ∀ b' a' : ZFSet.{0},
          (a' = ({{vN 0, vN 0}, {vN 0, vN 0}} : ZFSet.{0}) ∧ ETape b') →
            b = ({{a', a'}, {a', b'}} : ZFSet.{0})) → x2 = ({{a, a}, {a, b}} : ZFSet.{0})) → x1 = x2) ↔ _
  simp only [forall_eq, forall_eq', and_imp, forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂]


lemma val_of_mem_funSet {X Y g x y : ZFSet.{0}} (hg : g ∈ funSet X Y) (hx : x ∈ X)
    (hxy : ({{x, x}, {x, y}} : ZFSet.{0}) ∈ g) : Val y g x := by
  obtain ⟨_, hfun⟩ := (mem_funSet X Y g).1 hg
  obtain ⟨y0, _, huniq⟩ := hfun x hx
  have hy : y = y0 := huniq y hxy
  unfold Val
  intro z
  constructor
  · intro hz
    exact ⟨ZFSet.mem_sUnion.2 ⟨y, (mem_rng g y).2 ⟨x, hxy⟩, hz⟩, y, hz, hxy⟩
  · rintro ⟨_, u, hzu, hxu⟩
    have hu : u = y0 := huniq u hxu
    rw [hy, ← hu]; exact hzu

/-- For a genuine function, the upstream `value` is ordinary function application. -/
lemma val_iff_of_mem_funSet {X Y g x y v : ZFSet.{0}} (hg : g ∈ funSet X Y) (hx : x ∈ X)
    (hxy : ({{x, x}, {x, y}} : ZFSet.{0}) ∈ g) : Val v g x ↔ v = y := by
  constructor
  · intro hv
    have hy := val_of_mem_funSet hg hx hxy
    exact ZFSet.ext fun z => by rw [hv z, hy z]
  · rintro rfl; exact val_of_mem_funSet hg hx hxy


/-- The upstream `value` is uniquely determined. -/
lemma val_unique {v w f x : ZFSet.{0}} (hv : Val v f x) (hw : Val w f x) : v = w :=
  ZFSet.ext fun z => by rw [hv z, hw z]


/-- Injectivity of the upstream pair encoding. -/
lemma kpair_inj {a b c d : ZFSet.{0}}
    (h : ({{a, a}, {a, b}} : ZFSet.{0}) = {{c, c}, {c, d}}) : a = c ∧ b = d := by
  have mem2 : ∀ {x y z : ZFSet.{0}}, z ∈ ({x, y} : ZFSet.{0}) ↔ z = x ∨ z = y := by
    intro x y z; simp [ZFSet.mem_insert_iff, ZFSet.mem_singleton]
  have hac : a = c := by
    have h1 : ({c, c} : ZFSet.{0}) ∈ ({{a, a}, {a, b}} : ZFSet.{0}) := by
      rw [h]; exact mem2.2 (Or.inl rfl)
    rcases mem2.1 h1 with h2 | h2
    · have : c ∈ ({a, a} : ZFSet.{0}) := by rw [← h2]; exact mem2.2 (Or.inl rfl)
      rcases mem2.1 this with h3 | h3 <;> exact h3.symm
    · have : c ∈ ({a, b} : ZFSet.{0}) := by rw [← h2]; exact mem2.2 (Or.inl rfl)
      rcases mem2.1 this with h3 | h3
      · exact h3.symm
      · have : a ∈ ({c, c} : ZFSet.{0}) := by rw [h2]; exact mem2.2 (Or.inl rfl)
        rcases mem2.1 this with h4 | h4 <;> exact h4
  subst hac
  refine ⟨rfl, ?_⟩
  have h1 : ({a, d} : ZFSet.{0}) ∈ ({{a, a}, {a, b}} : ZFSet.{0}) := by
    rw [h]; exact mem2.2 (Or.inr rfl)
  have h2 : ({a, b} : ZFSet.{0}) ∈ ({{a, a}, {a, d}} : ZFSet.{0}) := by
    rw [← h]; exact mem2.2 (Or.inr rfl)
  rcases mem2.1 h1 with h3 | h3
  · have hd : d ∈ ({a, a} : ZFSet.{0}) := by rw [← h3]; exact mem2.2 (Or.inr rfl)
    have hda : d = a := by rcases mem2.1 hd with h' | h' <;> exact h'
    rcases mem2.1 h2 with h4 | h4
    · have hb : b ∈ ({a, a} : ZFSet.{0}) := by rw [← h4]; exact mem2.2 (Or.inr rfl)
      have hba : b = a := by rcases mem2.1 hb with h' | h' <;> exact h'
      rw [hba, hda]
    · have hb : b ∈ ({a, d} : ZFSet.{0}) := by rw [← h4]; exact mem2.2 (Or.inr rfl)
      rcases mem2.1 hb with h5 | h5
      · rw [h5, hda]
      · exact h5
  · have hd : d ∈ ({a, b} : ZFSet.{0}) := by rw [← h3]; exact mem2.2 (Or.inr rfl)
    have hb : b ∈ ({a, d} : ZFSet.{0}) := by rw [h3]; exact mem2.2 (Or.inr rfl)
    rcases mem2.1 hb with h5 | h5
    · rcases mem2.1 hd with h6 | h6
      · rw [h5, h6]
      · exact h6.symm
    · exact h5


lemma pair_mem_prodSet {X Y x y : ZFSet.{0}} :
    ({{x, x}, {x, y}} : ZFSet.{0}) ∈ prodSet X Y ↔ x ∈ X ∧ y ∈ Y := by
  rw [mem_prodSet]
  constructor
  · rintro ⟨x', hx', y', hy', h⟩
    obtain ⟨rfl, rfl⟩ := kpair_inj h
    exact ⟨hx', hy'⟩
  · rintro ⟨hx, hy⟩
    exact ⟨x, hx, y, hy, rfl⟩


lemma mem_vN_succ_iff (k : ℕ) (y : ZFSet.{0}) : y ∈ vN (k + 1) ↔ y = vN k ∨ y ∈ vN k :=
  ZFSet.mem_insert_iff

lemma not_mem_vN_zero (y : ZFSet.{0}) : y ∉ vN 0 := ZFSet.notMem_empty y


lemma vN_ne_succ (k : ℕ) : vN k ≠ vN (k + 1) := fun h => ZFSet.mem_irrefl (vN k) (by
  have hm : vN k ∈ vN (k + 1) := (mem_vN_succ_iff k (vN k)).2 (Or.inl rfl)
  rw [← h] at hm
  exact hm)


lemma vN_succ_ne_zero (k : ℕ) : vN (k + 1) ≠ vN 0 := by
  intro h
  have hm : vN k ∈ vN (k + 1) := (mem_vN_succ_iff k (vN k)).2 (Or.inl rfl)
  rw [h] at hm
  exact not_mem_vN_zero _ hm


/-- The three direction codes (left, stay, right) are distinct. -/
lemma dir_codes_distinct : vN 0 ≠ vN 1 ∧ vN 1 ≠ vN 2 ∧ vN 0 ≠ vN 2 :=
  ⟨vN_ne_succ 0, vN_ne_succ 1, fun h => vN_succ_ne_zero 1 h.symm⟩


/-- State `0` is a valid state code for every machine with at least one state. -/
lemma zero_mem_vN_succ (k : ℕ) : vN 0 ∈ vN (k + 1) := by
  induction k with
  | zero => exact (mem_vN_succ_iff 0 (vN 0)).2 (Or.inl rfl)
  | succ k ih => exact (mem_vN_succ_iff (k + 1) (vN 0)).2 (Or.inr ih)


lemma vN_one_mem_vN_two : vN 1 ∈ vN 2 := (mem_vN_succ_iff 1 (vN 1)).2 (Or.inl rfl)


lemma vN_zero_mem_vN_two : vN 0 ∈ vN 2 := zero_mem_vN_succ 1


lemma vN_one_ne_zero : vN 1 ≠ vN 0 := vN_succ_ne_zero 0

lemma ev_env {ξ : Type*} {n : ℕ} {e e' : Fin n → ZFSet.{0}} (ε : ξ → ZFSet.{0})
    (φ : Semiformula ℒₛₑₜ ξ n) (h : ∀ i, e i = e' i) : ev R' e ε φ ↔ ev R' e' ε φ := by
  have : e = e' := funext h
  rw [this]

lemma ev_nff0 {m : ℕ} (φ : SetTheorySemisentence 1) (e : Fin (m + 1) → ZFSet.{0})
    (ε : Empty → ZFSet.{0}) :
    ev R' e ε (Semiformula.nestFormulaeFunc φ ![]) ↔ ev R' ![e 0] ε φ := by
  unfold Semiformula.nestFormulaeFunc
  simp only [allItr, ev_imp', Matrix.conj, ev_top', true_implies, ev_subst']
  apply ev_env
  intro i
  refine Fin.cases ?_ (fun j => Fin.elim0 j) i
  rfl

lemma ev_nff1 {m : ℕ} (φ : SetTheorySemisentence 2) (Ψ : SetTheorySemisentence (m + 1))
    (e : Fin (m + 1) → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε (Semiformula.nestFormulaeFunc φ ![Ψ]) ↔
      ∀ a : ZFSet.{0}, ev R' (Matrix.vecCons a (Matrix.vecTail e)) ε Ψ → ev R' ![e 0, a] ε φ := by
  unfold Semiformula.nestFormulaeFunc
  simp only [allItr, ev_all', ev_imp', Matrix.conj, ev_and', ev_top', and_true, ev_subst']
  refine forall_congr' fun a => ?_
  refine imp_congr (ev_env _ _ ?_) (ev_env _ _ ?_)
  · intro i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  · intro i; refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j; rfl

lemma ev_nff2 {m : ℕ} (φ : SetTheorySemisentence 3) (Ψ₁ Ψ₂ : SetTheorySemisentence (m + 1))
    (e : Fin (m + 1) → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε (Semiformula.nestFormulaeFunc φ ![Ψ₁, Ψ₂]) ↔
      ∀ b a : ZFSet.{0}, ev R' (Matrix.vecCons a (Matrix.vecTail e)) ε Ψ₁ →
        ev R' (Matrix.vecCons b (Matrix.vecTail e)) ε Ψ₂ → ev R' ![e 0, a, b] ε φ := by
  unfold Semiformula.nestFormulaeFunc
  simp only [allItr, ev_all', ev_imp', Matrix.conj, ev_and', ev_top', and_true, ev_subst', and_imp]
  refine forall_congr' fun b => forall_congr' fun a => ?_
  refine imp_congr (ev_env _ _ ?_) (imp_congr ?_ (ev_env _ _ ?_))
  · intro i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  · show ev R' _ ε (Ψ₂ ⇜ _) ↔ _
    rw [ev_subst']
    apply ev_env
    intro i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  · intro i; refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun l => Fin.elim0 l) k; rfl

lemma ev_nf1 {m : ℕ} (φ : SetTheorySemisentence 1) (Ψ : SetTheorySemisentence (m + 1))
    (e : Fin m → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε (Semiformula.nestFormulae φ ![Ψ]) ↔
      ∀ a : ZFSet.{0}, ev R' (Matrix.vecCons a e) ε Ψ → ev R' ![a] ε φ := by
  unfold Semiformula.nestFormulae
  simp only [allItr, ev_all', ev_imp', Matrix.conj, ev_and', ev_top', and_true, ev_subst']
  refine forall_congr' fun a => ?_
  refine imp_congr (ev_env _ _ ?_) (ev_env _ _ ?_)
  · intro i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  · intro i; refine Fin.cases ?_ (fun j => Fin.elim0 j) i; rfl

lemma ev_nf2 {m : ℕ} (φ : SetTheorySemisentence 2) (Ψ₁ Ψ₂ : SetTheorySemisentence (m + 1))
    (e : Fin m → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε (Semiformula.nestFormulae φ ![Ψ₁, Ψ₂]) ↔
      ∀ b a : ZFSet.{0}, ev R' (Matrix.vecCons a e) ε Ψ₁ →
        ev R' (Matrix.vecCons b e) ε Ψ₂ → ev R' ![a, b] ε φ := by
  unfold Semiformula.nestFormulae
  simp only [allItr, ev_all', ev_imp', Matrix.conj, ev_and', ev_top', and_true, ev_subst', and_imp]
  refine forall_congr' fun b => forall_congr' fun a => ?_
  refine imp_congr (ev_env _ _ ?_) (imp_congr ?_ (ev_env _ _ ?_))
  · intro i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  · show ev R' _ ε (Ψ₂ ⇜ _) ↔ _
    rw [ev_subst']
    apply ev_env
    intro i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  · intro i; refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j; rfl


noncomputable def SI (x : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.sep (fun z => ∀ y ∈ x, z ∈ y) (ZFSet.sUnion x)

noncomputable def P1 (x : ZFSet.{0}) : ZFSet.{0} := ZFSet.sUnion (SI x)

noncomputable def P2 (x : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.sUnion (ZFSet.sep (fun z => z ∈ SI x → ZFSet.sUnion x = SI x) (ZFSet.sUnion x))

noncomputable def VAL (f x : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.sep (fun z => ∃ y, z ∈ y ∧ ({{x, x}, {x, y}} : ZFSet.{0}) ∈ f) (ZFSet.sUnion (rng f))

lemma mem_SI (x z : ZFSet.{0}) : z ∈ SI x ↔ (∃ y, y ∈ x) ∧ ∀ y ∈ x, z ∈ y := by
  unfold SI
  rw [ZFSet.mem_sep, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨⟨y, hy, _⟩, h⟩; exact ⟨⟨y, hy⟩, h⟩
  · rintro ⟨⟨y, hy⟩, h⟩; exact ⟨⟨y, hy, h y hy⟩, h⟩

lemma SI_char (x i : ZFSet.{0}) :
    (∀ z, z ∈ i ↔ (∃ y, y ∈ x) ∧ ∀ y ∈ x, z ∈ y) ↔ i = SI x := by
  constructor
  · intro h; exact ZFSet.ext fun z => by rw [h z, mem_SI]
  · intro h z; rw [h, mem_SI]

lemma ev_pi1 (e : Fin 2 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε kpair.π₁.dfn ↔ e 0 = P1 (e 1) := by
  unfold kpair.π₁.dfn
  simp only [ev_all', ev_imp', ev_subst', ev_sInter, ev_sUnion]
  show (∀ i, (∀ z, z ∈ i ↔ (∃ y, y ∈ e 1) ∧ ∀ y ∈ e 1, z ∈ y) → e 0 = ZFSet.sUnion i) ↔ _
  simp only [SI_char, forall_eq]
  exact Iff.rfl

lemma ev_pi2 (e : Fin 2 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε kpair.π₂.dfn ↔ e 0 = P2 (e 1) := by
  unfold kpair.π₂.dfn
  simp only [ev_all', ev_imp', ev_subst', ev_sInter, ev_sUnion, ev_iff', ev_mem', ev_and', ev_eq',
    tval_bvar]
  show (∀ u, u = ZFSet.sUnion (e 1) → ∀ i, (∀ z, z ∈ i ↔ (∃ y, y ∈ e 1) ∧ ∀ y ∈ e 1, z ∈ y) →
      ∀ s, (∀ z, z ∈ s ↔ z ∈ u ∧ (z ∈ i → u = i)) → e 0 = ZFSet.sUnion s) ↔ _
  have hs : ∀ s : ZFSet.{0}, (∀ z, z ∈ s ↔ z ∈ ZFSet.sUnion (e 1) ∧
      (z ∈ SI (e 1) → ZFSet.sUnion (e 1) = SI (e 1))) ↔
      s = ZFSet.sep (fun z => z ∈ SI (e 1) → ZFSet.sUnion (e 1) = SI (e 1))
        (ZFSet.sUnion (e 1)) := by
    intro s
    constructor
    · intro h; exact ZFSet.ext fun z => by rw [h z, ZFSet.mem_sep]
    · intro h z; rw [h, ZFSet.mem_sep]
  simp only [SI_char, forall_eq, hs]
  exact Iff.rfl

lemma P1_kp_aux (a b p : ZFSet.{0}) (hp : p = P1 ({{a, a}, {a, b}} : ZFSet.{0})) : p = a := by
  have h := ev_pi1_pair a b p ![p, ({{a, a}, {a, b}} : ZFSet.{0})] rfl rfl Empty.elim
  exact h.1 ((ev_pi1 _ _).2 hp)

lemma P1_kp (a b : ZFSet.{0}) : P1 ({{a, a}, {a, b}} : ZFSet.{0}) = a := P1_kp_aux a b _ rfl

lemma P2_kp_aux (a b p : ZFSet.{0}) (hp : p = P2 ({{a, a}, {a, b}} : ZFSet.{0})) : p = b := by
  have h := ev_pi2_pair a b p ![p, ({{a, a}, {a, b}} : ZFSet.{0})] rfl rfl Empty.elim
  exact h.1 ((ev_pi2 _ _).2 hp)

lemma P2_kp (a b : ZFSet.{0}) : P2 ({{a, a}, {a, b}} : ZFSet.{0}) = b := P2_kp_aux a b _ rfl

lemma vh_vt {α : Type*} {n : ℕ} (e : Fin (n + 2) → α) : Matrix.vecHead (Matrix.vecTail e) = e 1 := rfl

lemma mem_VAL (f x z : ZFSet.{0}) : z ∈ VAL f x ↔
    z ∈ ZFSet.sUnion (rng f) ∧ ∃ y, z ∈ y ∧ ({{x, x}, {x, y}} : ZFSet.{0}) ∈ f := by
  unfold VAL; rw [ZFSet.mem_sep]

lemma Val_iff (v f x : ZFSet.{0}) : Val v f x ↔ v = VAL f x := by
  unfold Val
  constructor
  · intro h; exact ZFSet.ext fun z => by rw [h z, mem_VAL]
  · intro h z; rw [h, mem_VAL]

lemma ev_value_fn (e : Fin 3 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε value.dfn ↔ e 0 = VAL (e 1) (e 2) := by
  rw [ev_value]; exact Val_iff _ _ _

lemma ev_function_fn (e : Fin 3 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε function.dfn ↔ e 0 = funSet (e 2) (e 1) := by
  rw [ev_function]; exact FunSet_iff _ _ _

lemma ev_prod_fn (e : Fin 3 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε prod.dfn ↔ e 0 = prodSet (e 1) (e 2) := by
  rw [ev_prod]; exact prodChar_iff _ _ _

/-- The integers of the encoding. -/
noncomputable def INT : ZFSet.{0} := prodSet (vN 2) ZFSet.omega

lemma ev_integers_fn (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε Constant14.integers ↔ e 0 = INT := ev_integers' e ε

/-- Semantic content of the upstream `integerSucc.dfn`. -/
def ISUCC (z' z : ZFSet.{0}) : Prop :=
  (z ∈ INT ∧ ((P1 z = vN 0 ∧ z' = ({{vN 0, vN 0}, {vN 0, insert (P2 z) (P2 z)}} : ZFSet.{0})) ∨
     (P1 z = vN 1 ∧ ((P2 z = vN 0 ∧ z' = ({{vN 0, vN 0}, {vN 0, vN 0}} : ZFSet.{0})) ∨
        ∃ k ∈ ZFSet.omega.{0}, P2 z = insert k k ∧ z' = ({{vN 1, vN 1}, {vN 1, k}} : ZFSet.{0}))))) ∨
  (z ∉ INT ∧ z' = ({{vN 0, vN 0}, {vN 0, vN 0}} : ZFSet.{0}))

lemma ev_integerSucc (e : Fin 2 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε Constant14.integerSucc.dfn ↔ ISUCC (e 0) (e 1) := by
  unfold Constant14.integerSucc.dfn ISUCC
  simp only [ev_all', ev_exs', ev_imp', ev_and', ev_or', ev_not', ev_iff', ev_top', ev_eq', ev_mem',
    ev_ballMem, ev_bexsMem, tval_bvar, ev_subst', ev_nff0, ev_nff1, ev_nff2, ev_nf1, ev_nf2,
    ev_kpair, ev_pi1, ev_pi2, ev_value_fn, ev_isSucc, ev_numeral, ev_integers_fn, ev_isω,
    ev_integerZero, ev_function_fn, ev_prod_fn, vh_vt, Matrix.cons_val,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_succ, Matrix.head_cons, forall_eq, forall_eq', and_imp,
    forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂]

/-- Semantic content of the upstream `integerPred.dfn`. -/
def IPRED (z' z : ZFSet.{0}) : Prop :=
  (z ∈ INT ∧ z' ∈ INT ∧ ISUCC z z') ∨ (z ∉ INT ∧ z' = ({{vN 0, vN 0}, {vN 0, vN 0}} : ZFSet.{0}))

lemma ev_integerPred (e : Fin 2 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε Constant14.integerPred.dfn ↔ IPRED (e 0) (e 1) := by
  unfold Constant14.integerPred.dfn IPRED
  simp only [ev_all', ev_exs', ev_imp', ev_and', ev_or', ev_not', ev_iff', ev_top', ev_eq', ev_mem',
    ev_ballMem, ev_bexsMem, tval_bvar, ev_subst', ev_nff0, ev_nff1, ev_nff2, ev_nf1, ev_nf2,
    ev_kpair, ev_pi1, ev_pi2, ev_value_fn, ev_isSucc, ev_numeral, ev_integers_fn, ev_isω,
    ev_integerZero, ev_function_fn, ev_prod_fn, ev_integerSucc, vh_vt, Matrix.cons_val,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_succ, Matrix.head_cons, forall_eq, forall_eq', and_imp,
    forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂]


/-- The configuration set of the encoding. -/
noncomputable def CS (n : ℕ) : ZFSet.{0} := prodSet (vN n) (prodSet INT (funSet INT (vN 2)))

lemma ev_configSet_fn (n : ℕ) (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε (Constant14.configSet n) ↔ e 0 = CS n := ev_configSet n e ε

/-- Semantic content of the upstream `nextConfig`. -/
def NC (n : ℕ) (T z' z : ZFSet.{0}) : Prop :=
  z ∈ CS n ∧ z' ∈ CS n ∧
  ∃ t, t = VAL T ({{P1 z, P1 z}, {P1 z, VAL (P2 (P2 z)) (P1 (P2 z))}} : ZFSet.{0}) ∧
    P1 z' = P1 t ∧
    ((P2 (P2 t) = vN 0 ∧ IPRED (P1 (P2 z')) (P1 (P2 z))) ∨
     (P2 (P2 t) = vN 1 ∧ P1 (P2 z') = P1 (P2 z)) ∨
     (P2 (P2 t) = vN 2 ∧ ISUCC (P1 (P2 z')) (P1 (P2 z)))) ∧
    VAL (P2 (P2 z')) (P1 (P2 z)) = P1 (P2 t) ∧
    ∀ k ∈ INT, k ≠ P1 (P2 z) → VAL (P2 (P2 z')) k = VAL (P2 (P2 z)) k

lemma ev_nextConfig (n : ℕ) (instr : SetTheorySemisentence 1) (T : ZFSet.{0})
    (hT : ∀ (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}), ev R' e ε instr ↔ e 0 = T)
    (e : Fin 2 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε (Constant14.nextConfig n instr) ↔ NC n T (e 0) (e 1) := by
  unfold Constant14.nextConfig NC
  simp only [ev_all', ev_exs', ev_imp', ev_and', ev_or', ev_not', ev_iff', ev_top', ev_eq', ev_mem',
    ev_ballMem, ev_bexsMem, tval_bvar, ev_subst', ev_nff0, ev_nff1, ev_nff2, ev_nf1, ev_nf2,
    ev_kpair, ev_pi1, ev_pi2, ev_value_fn, ev_isSucc, ev_numeral, ev_integers_fn, ev_isω,
    ev_integerZero, ev_function_fn, ev_prod_fn, ev_integerSucc, ev_integerPred, ev_configSet_fn, hT,
    vh_vt, Matrix.cons_val,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_succ, Matrix.head_cons, forall_eq, forall_eq', and_imp,
    forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂]
  exact Iff.rfl

lemma ev_nextStep (n : ℕ) (instr : SetTheorySemisentence 1) (T : ZFSet.{0})
    (hT : ∀ (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}), ev R' e ε instr ↔ e 0 = T)
    (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε (Constant14.nextStep n instr) ↔
      ∀ w, w ∈ e 0 ↔ ∃ z ∈ CS n, ∃ z' ∈ CS n,
        w = ({{z, z}, {z, z'}} : ZFSet.{0}) ∧ NC n T z' z := by
  unfold Constant14.nextStep
  simp only [ev_all', ev_exs', ev_imp', ev_and', ev_or', ev_not', ev_iff', ev_top', ev_eq', ev_mem',
    ev_ballMem, ev_bexsMem, tval_bvar, ev_subst', ev_nff0, ev_nff1, ev_nff2, ev_nf1, ev_nf2,
    ev_kpair, ev_pi1, ev_pi2, ev_value_fn, ev_isSucc, ev_numeral, ev_integers_fn, ev_isω,
    ev_integerZero, ev_function_fn, ev_prod_fn, ev_configSet_fn, ev_nextConfig n instr T hT,
    vh_vt, Matrix.cons_val,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_succ, Matrix.head_cons, forall_eq, forall_eq', and_imp,
    forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂]


/-- Semantic content of the upstream `orbit`. -/
def ORB (O f x : ZFSet.{0}) : Prop :=
  (∃ X Y : ZFSet.{0}, f ∈ funSet X Y) ∧
    ∀ z, z ∈ O ↔ ∀ A : ZFSet.{0}, (x ∈ A ∧ ∀ y ∈ A, VAL f y ∈ A) → z ∈ A

lemma ev_orbit_fn (e : Fin 3 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε Constant14.orbit ↔ ORB (e 0) (e 1) (e 2) := by
  rw [ev_orbit]
  unfold ORB
  simp only [FunSet_iff, forall_eq, Val_iff]

/-- The blank tape: the constant-zero function on the integers. -/
noncomputable def ETAPE : ZFSet.{0} := prodSet (prodSet (vN 2) ZFSet.omega) {vN 0}

lemma ETape_iff (t : ZFSet.{0}) : ETape t ↔ t = ETAPE := by
  unfold ETape
  constructor
  · rintro ⟨hfun, hval⟩
    have hfun' := (mem_funSet _ _ _).1 hfun
    apply ZFSet.ext
    intro w
    unfold ETAPE
    rw [mem_prodSet]
    constructor
    · intro hw
      obtain ⟨x, hx, y, hy, rfl⟩ := (mem_prodSet _ _ _).1 (hfun'.1 w hw)
      have hv := val_of_mem_funSet hfun hx hw
      have hy0 := hval x hx y hv
      exact ⟨x, hx, y, by rw [hy0]; exact ZFSet.mem_singleton.2 rfl, rfl⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      rw [ZFSet.mem_singleton] at hy
      subst hy
      obtain ⟨y, hxy, _⟩ := hfun'.2 x hx
      have hv := val_of_mem_funSet hfun hx hxy
      have hy0 := hval x hx y hv
      rw [hy0] at hxy
      exact hxy
  · rintro rfl
    have hmem : ETAPE ∈ funSet (prodSet (vN 2) ZFSet.omega) (vN 2) := by
      rw [mem_funSet]
      constructor
      · intro w hw
        obtain ⟨x, hx, y, hy, rfl⟩ := (mem_prodSet _ _ _).1 hw
        rw [ZFSet.mem_singleton] at hy; subst hy
        exact pair_mem_prodSet.2 ⟨hx, vN_zero_mem_vN_two⟩
      · intro x hx
        refine ⟨vN 0, pair_mem_prodSet.2 ⟨hx, ZFSet.mem_singleton.2 rfl⟩, fun z hz => ?_⟩
        exact ZFSet.mem_singleton.1 (pair_mem_prodSet.1 hz).2
    refine ⟨hmem, fun i hi v hv => ?_⟩
    exact (val_iff_of_mem_funSet hmem hi
      (pair_mem_prodSet.2 ⟨hi, ZFSet.mem_singleton.2 rfl⟩)).1 hv

/-- The encoded initial configuration. -/
noncomputable def X0 : ZFSet.{0} :=
  {{vN 0, vN 0}, {vN 0, ({{({{vN 0, vN 0}, {vN 0, vN 0}} : ZFSet.{0}), {{vN 0, vN 0}, {vN 0, vN 0}}},
    {({{vN 0, vN 0}, {vN 0, vN 0}} : ZFSet.{0}), ETAPE}} : ZFSet.{0})}}

lemma ev_initialConfig_fn (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}) :
    ev R' e ε Constant14.initialConfig ↔ e 0 = X0 := by
  rw [ev_initialConfig]
  simp only [ETape_iff, forall_eq]
  exact Iff.rfl

lemma ev_halts {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) (T : ZFSet.{0})
    (hT : ∀ (e : Fin 1 → ZFSet.{0}) (ε : Empty → ZFSet.{0}),
      ev R' e ε (Constant14.instructionTable M) ↔ e 0 = T) :
    SatS R' (Constant14.halts M) ↔
      ∃ m ∈ INT, ∃ g ∈ funSet INT (vN 2), ∀ O : ZFSet.{0},
        (∀ f : ZFSet.{0}, (∀ w, w ∈ f ↔ ∃ z ∈ CS (n + 1), ∃ z' ∈ CS (n + 1),
            w = ({{z, z}, {z, z'}} : ZFSet.{0}) ∧ NC (n + 1) T z' z) → ORB O f X0) →
          ({{vN n, vN n}, {vN n, ({{m, m}, {m, g}} : ZFSet.{0})}} : ZFSet.{0}) ∈ O := by
  unfold SatS Constant14.halts
  simp only [ev_all', ev_exs', ev_imp', ev_and', ev_or', ev_not', ev_iff', ev_top', ev_eq', ev_mem',
    ev_ballMem, ev_bexsMem, tval_bvar, ev_subst', ev_nff0, ev_nff1, ev_nff2, ev_nf1, ev_nf2,
    ev_kpair, ev_pi1, ev_pi2, ev_value_fn, ev_isSucc, ev_numeral, ev_integers_fn, ev_isω,
    ev_integerZero, ev_function_fn, ev_prod_fn, ev_configSet_fn, ev_orbit_fn, ev_initialConfig_fn,
    ev_nextStep (n + 1) _ T hT,
    vh_vt, Matrix.cons_val,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.cons_val_succ, Matrix.head_cons, forall_eq, forall_eq', and_imp,
    forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂]
  refine exists_congr fun m => and_congr Iff.rfl (exists_congr fun g => and_congr Iff.rfl
    (forall_congr' fun O => imp_congr
      ⟨fun h f hf => h X0 f hf rfl, fun h b a ha hb => by subst hb; exact h a ha⟩ Iff.rfl))


/-- Any truth predicate on `ZFSet` obeying Tarski's clauses is the evaluation `ev`. -/
lemma tr_iff_ev (tr : ∀ {m : ℕ}, (Fin m → ZFSet.{0}) → Semisentence ℒₛₑₜ m → Prop)
    (h1 : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}), tr e Semiformula.verum)
    (h2 : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}), ¬ tr e Semiformula.falsum)
    (h3 : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (i j : Fin m),
      (tr e (Semiformula.rel Language.Set.Rel.eq ![Semiterm.bvar i, Semiterm.bvar j]) ↔ e i = e j))
    (h4 : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (i j : Fin m),
      (tr e (Semiformula.rel Language.Set.Rel.mem ![Semiterm.bvar i, Semiterm.bvar j]) ↔ e i ∈ e j))
    (h5 : ∀ {m k : ℕ} (e : Fin m → ZFSet.{0}) (r : Language.Set.Rel k)
      (v : Fin k → Semiterm ℒₛₑₜ Empty m),
      (tr e (Semiformula.nrel r v) ↔ ¬ tr e (Semiformula.rel r v)))
    (h6 : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (φ ψ : Semisentence ℒₛₑₜ m),
      (tr e (Semiformula.and φ ψ) ↔ tr e φ ∧ tr e ψ))
    (h7 : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (φ ψ : Semisentence ℒₛₑₜ m),
      (tr e (Semiformula.or φ ψ) ↔ tr e φ ∨ tr e ψ))
    (h8 : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : Semisentence ℒₛₑₜ (m + 1)),
      (tr e (Semiformula.all φ) ↔ ∀ d, tr (Matrix.vecCons d e) φ))
    (h9 : ∀ {m : ℕ} (e : Fin m → ZFSet.{0}) (φ : Semisentence ℒₛₑₜ (m + 1)),
      (tr e (Semiformula.exs φ) ↔ ∃ d, tr (Matrix.vecCons d e) φ)) :
    ∀ {m : ℕ} (φ : Semisentence ℒₛₑₜ m) (e : Fin m → ZFSet.{0}),
      tr e φ ↔ ev R' e (Empty.elim : Empty → ZFSet.{0}) φ := by
  have hv : ∀ {m : ℕ} (t : Semiterm ℒₛₑₜ Empty m), ∃ i, t = Semiterm.bvar i := by
    intro m t
    cases t with
    | bvar i => exact ⟨i, rfl⟩
    | fvar x => exact x.elim
    | func f _ => exact (f : Empty).elim
  have rel_case : ∀ {m k : ℕ} (r : Language.Set.Rel k) (v : Fin k → Semiterm ℒₛₑₜ Empty m)
      (e : Fin m → ZFSet.{0}),
      tr e (Semiformula.rel r v) ↔ ev R' e (Empty.elim : Empty → ZFSet.{0}) (Semiformula.rel r v) := by
    intro m k r v e
    cases r with
    | eq =>
      obtain ⟨i, hi⟩ := hv (v 0)
      obtain ⟨j, hj⟩ := hv (v 1)
      have hvv : v = ![Semiterm.bvar i, Semiterm.bvar j] := by
        funext k; fin_cases k
        · exact hi
        · exact hj
      rw [hvv, h3]
      exact Iff.rfl
    | mem =>
      obtain ⟨i, hi⟩ := hv (v 0)
      obtain ⟨j, hj⟩ := hv (v 1)
      have hvv : v = ![Semiterm.bvar i, Semiterm.bvar j] := by
        funext k; fin_cases k
        · exact hi
        · exact hj
      rw [hvv, h4]
      exact Iff.rfl
  intro m φ
  induction φ with
  | verum => intro e; exact ⟨fun _ => trivial, fun _ => h1 e⟩
  | falsum => intro e; exact ⟨fun h => (h2 e h).elim, fun h => h.elim⟩
  | rel r v => intro e; exact rel_case r v e
  | nrel r v => intro e; rw [h5]; exact not_congr (rel_case r v e)
  | and φ ψ ih1 ih2 => intro e; rw [h6]; exact and_congr (ih1 e) (ih2 e)
  | or φ ψ ih1 ih2 => intro e; rw [h7]; exact or_congr (ih1 e) (ih2 e)
  | all φ ih => intro e; rw [h8]; exact forall_congr' fun d => ih _
  | exs φ ih => intro e; rw [h9]; exact exists_congr fun d => ih _

lemma defines_unique {ψ : SetTheorySemisentence 1} {A B : ZFSet.{0}}
    (hA : Defines ψ A) (hB : Defines ψ B) : A = B := by
  have h1 := (hA ![A] Empty.elim).2 rfl
  exact (hB ![A] Empty.elim).1 h1

lemma exists_vals (l : List (SetTheorySemisentence 1)) (h : ∀ x ∈ l, ∃ A, Defines x A) :
    ∃ vals, List.Forall₂ Defines l vals := by
  induction l with
  | nil => exact ⟨[], List.Forall₂.nil⟩
  | cons x xs ih =>
    obtain ⟨A, hA⟩ := h x List.mem_cons_self
    obtain ⟨vs, hvs⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    exact ⟨A :: vs, List.Forall₂.cons hA hvs⟩

lemma mem_foldr_vals (vals : List ZFSet.{0}) (z : ZFSet.{0}) :
    z ∈ vals.foldr (fun A B => ZFSet.sUnion {{A, A}, B}) ∅ ↔ z ∈ vals := by
  induction vals with
  | nil => simp
  | cons A vs ih =>
    rw [List.foldr_cons, ZFSet.mem_sUnion, List.mem_cons]
    constructor
    · rintro ⟨w, hw, hz⟩
      rcases ZFSet.mem_insert_iff.1 hw with rfl | hw
      · left; simpa using hz
      · rw [ZFSet.mem_singleton] at hw; subst hw; exact Or.inr (ih.1 hz)
    · rintro (rfl | h)
      · exact ⟨{z, z}, by simp, by simp⟩
      · exact ⟨_, by simp, ih.2 h⟩

lemma forall₂_mem_iff {l : List (SetTheorySemisentence 1)} {vals : List ZFSet.{0}}
    (h : List.Forall₂ Defines l vals) (z : ZFSet.{0}) : z ∈ vals ↔ ∃ x ∈ l, Defines x z := by
  induction h with
  | nil => simp
  | cons hx _ ih =>
    rw [List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨y, hy, hd⟩)
      · exact ⟨_, List.mem_cons_self, hx⟩
      · exact ⟨y, List.mem_cons_of_mem _ hy, hd⟩
    · rintro ⟨y, hy, hd⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact Or.inl (defines_unique hd hx)
      · exact Or.inr ⟨y, hy, hd⟩

/-- The value in `ZFSet` of one row of the instruction table. -/
noncomputable def EV (q s q' w d : ℕ) : ZFSet.{0} :=
  let P : ZFSet.{0} := {{vN q, vN q}, {vN q, vN s}}
  let T : ZFSet.{0} := {{vN q', vN q'}, {vN q', ({{vN w, vN w}, {vN w, vN d}} : ZFSet.{0})}}
  ({{P, P}, {P, T}} : ZFSet.{0})

lemma mem_transitionEntries {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (x : SetTheorySemisentence 1) :
    x ∈ Constant14.transitionEntries M ↔
      (∃ q : Fin n, ∃ s : Fin 2, x = Constant14.transitionEntry q.val s.val
        (Constant14.transitionCode M q s).1 (Constant14.transitionCode M q s).2.1
        (Constant14.transitionCode M q s).2.2) ∨
      (∃ s : Fin 2, x = Constant14.transitionEntry n s.val n s.val 1) := by
  unfold Constant14.transitionEntries
  simp only [List.mem_append, List.mem_flatten, List.mem_ofFn]
  constructor
  · rintro (⟨l, ⟨q, rfl⟩, hx⟩ | ⟨s, rfl⟩)
    · simp only [List.mem_ofFn] at hx
      obtain ⟨s, rfl⟩ := hx
      exact Or.inl ⟨q, s, rfl⟩
    · exact Or.inr ⟨s, rfl⟩
  · rintro (⟨q, s, rfl⟩ | ⟨s, rfl⟩)
    · refine Or.inl ⟨_, ⟨q, rfl⟩, ?_⟩
      simp only [List.mem_ofFn]
      exact ⟨s, rfl⟩
    · exact Or.inr ⟨s, rfl⟩

/-- The instruction table of `M` denotes a set `T` in `ZFSet` whose elements are exactly the rows. -/
lemma exists_table {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∃ T : ZFSet.{0}, Defines (Constant14.instructionTable M) T ∧
      ∀ z, z ∈ T ↔
        (∃ q : Fin n, ∃ s : Fin 2, z = EV q.val s.val (Constant14.transitionCode M q s).1
          (Constant14.transitionCode M q s).2.1 (Constant14.transitionCode M q s).2.2) ∨
        (∃ s : Fin 2, z = EV n s.val n s.val 1) := by
  have hall : ∀ x ∈ Constant14.transitionEntries M, ∃ A, Defines x A := by
    intro x hx
    rcases (mem_transitionEntries M x).1 hx with ⟨q, s, rfl⟩ | ⟨s, rfl⟩
    · exact ⟨_, defines_transitionEntry _ _ _ _ _⟩
    · exact ⟨_, defines_transitionEntry _ _ _ _ _⟩
  obtain ⟨vals, hvals⟩ := exists_vals _ hall
  refine ⟨_, defines_finiteSet hvals, fun z => ?_⟩
  rw [mem_foldr_vals, forall₂_mem_iff hvals]
  constructor
  · rintro ⟨x, hx, hd⟩
    rcases (mem_transitionEntries M x).1 hx with ⟨q, s, rfl⟩ | ⟨s, rfl⟩
    · exact Or.inl ⟨q, s, defines_unique hd (defines_transitionEntry _ _ _ _ _)⟩
    · exact Or.inr ⟨s, defines_unique hd (defines_transitionEntry _ _ _ _ _)⟩
  · rintro (⟨q, s, rfl⟩ | ⟨s, rfl⟩)
    · exact ⟨_, (mem_transitionEntries M _).2 (Or.inl ⟨q, s, rfl⟩), defines_transitionEntry _ _ _ _ _⟩
    · exact ⟨_, (mem_transitionEntries M _).2 (Or.inr ⟨s, rfl⟩), defines_transitionEntry _ _ _ _ _⟩

/-- The standard-model meaning of `halts M`, with the instruction table made explicit. -/
theorem halts_sem {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n)) :
    ∃ T : ZFSet.{0},
      (∀ z, z ∈ T ↔
        (∃ q : Fin n, ∃ s : Fin 2, z = EV q.val s.val (Constant14.transitionCode M q s).1
          (Constant14.transitionCode M q s).2.1 (Constant14.transitionCode M q s).2.2) ∨
        (∃ s : Fin 2, z = EV n s.val n s.val 1)) ∧
      (SatS R' (Constant14.halts M) ↔
        ∃ m ∈ INT, ∃ g ∈ funSet INT (vN 2), ∀ O : ZFSet.{0},
          (∀ f : ZFSet.{0}, (∀ w, w ∈ f ↔ ∃ z ∈ CS (n + 1), ∃ z' ∈ CS (n + 1),
              w = ({{z, z}, {z, z'}} : ZFSet.{0}) ∧ NC (n + 1) T z' z) → ORB O f X0) →
            ({{vN n, vN n}, {vN n, ({{m, m}, {m, g}} : ZFSet.{0})}} : ZFSet.{0}) ∈ O) := by
  obtain ⟨T, hT, hmem⟩ := exists_table M
  exact ⟨T, hmem, ev_halts M T hT⟩

end C14Faith

namespace C14Aux

open C14Sem C14Model C14Faith

/-- The defining set of `C14`. -/
def S : Set ℕ := {n | ∃ _ : NeZero n, ∃ M : Machine (Fin 2) (Fin n),
    𝗭𝗙𝗖 ⊬ Constant14.halts M ∧ 𝗭𝗙𝗖 ⊬ ∼Constant14.halts M}

lemma C14_eq : Constant14.C14 = sInf S := rfl

lemma four_le_of (hne : S.Nonempty) (hsmall : ∀ n ∈ S, 4 ≤ n) : 4 ≤ Constant14.C14 := by
  rw [C14_eq]
  exact le_csInf hne hsmall

/-- Every machine that `ZFSet` says does not halt is not provably halting. -/
lemma not_provable_halts_of_zfset {n : ℕ} [NeZero n] (M : Machine (Fin 2) (Fin n))
    (h : ¬ C14Sem.SatS C14Model.R' (Constant14.halts M)) : 𝗭𝗙𝗖 ⊬ Constant14.halts M :=
  C14Sem.unprovable_of_model C14Model.R' C14Model.zfsetModel h

/-- GAP 1 (Sigma-1 completeness for small machines): not proved. -/
lemma gap_sigma1_complete (n : ℕ) [NeZero n] (M : Machine (Fin 2) (Fin n)) (hn : n < 4)
    (h : M.IsHalting) : FFL.Entailment.Provable 𝗭𝗙𝗖 (Constant14.halts M) := by
  sorry

/-- GAP 2 (ZFC refutes halting of every non-halting machine with at most 3 states): not proved. -/
lemma gap_small_nonhalting (n : ℕ) [NeZero n] (M : Machine (Fin 2) (Fin n)) (hn : n < 4)
    (h : ¬ M.IsHalting) : FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M) := by
  sorry

/-- GAP 3 (the encoding is faithful in the standard model `ZFSet`): not proved.
`C14Faith.halts_sem` reduces it to a plain statement about `ZFSet`. -/
lemma gap_standard_model (n : ℕ) [NeZero n] (M : Machine (Fin 2) (Fin n)) (h : ¬ M.IsHalting) :
    ¬ SatS R' (Constant14.halts M) := by
  sorry

/-- GAP 4 (Goedel: some non-halting machine whose non-halting ZFC cannot prove): not proved. -/
lemma gap_goedel : ∃ (n : ℕ) (_ : NeZero n) (M : Machine (Fin 2) (Fin n)),
    ¬ M.IsHalting ∧ ¬ FFL.Entailment.Provable 𝗭𝗙𝗖 (∼Constant14.halts M) := by
  sorry

end C14Aux

theorem OMA.solution : type_of% @Constant14.c14_ge_4 := by
  apply C14Aux.four_le_of
  · obtain ⟨n, hn, M, hnh, hnp⟩ := C14Aux.gap_goedel
    exact ⟨n, hn, M, C14Aux.not_provable_halts_of_zfset M (C14Aux.gap_standard_model n M hnh), hnp⟩
  · rintro n ⟨hn, M, hu1, hu2⟩
    by_contra hlt
    have hlt' : n < 4 := lt_of_not_ge hlt
    by_cases hh : M.IsHalting
    · exact hu1 (C14Aux.gap_sigma1_complete n M hlt' hh)
    · exact hu2 (C14Aux.gap_small_nonhalting n M hlt' hh)
