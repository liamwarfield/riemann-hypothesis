module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGl
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PJmComm
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PPiQdet
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PStepFormula
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PStepChar
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PChain
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PColAnti
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransFin
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAll
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PWallAlg
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGK
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSWStart
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PContract
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PYoung
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PKType

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PHeight
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace HeightVanishing

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def ht (w : List (Fin n × Fin n)) : ℤ := (w.map fun x => ((x.2 : ℕ) : ℤ) - ((x.1 : ℕ) : ℤ)).sum

def word (E : Fin n → Fin n → Module.End ℂ M) (w : List (Fin n × Fin n)) : Module.End ℂ M :=
  (w.map fun x => E x.1 x.2).prod

def W (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (h : ℤ) : Submodule ℂ (Module.End ℂ M) :=
  Submodule.span ℂ {A | ∃ w, w.length ≤ k ∧ ht w = h ∧ word E w = A}

variable (E : Fin n → Fin n → Module.End ℂ M)

theorem ht_cons (x : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    ht (x :: w) = (((x.2 : ℕ) : ℤ) - ((x.1 : ℕ) : ℤ)) + ht w := by
  simp [ht]

theorem word_cons (x : Fin n × Fin n) (w : List (Fin n × Fin n)) : word E (x :: w) = E x.1 x.2 * word E w := by
  simp [word]

theorem word_mem {k : ℕ} {h : ℤ} (w : List (Fin n × Fin n)) (hk : w.length ≤ k) (hh : ht w = h) :
    word E w ∈ W E k h := Submodule.subset_span ⟨w, hk, hh, rfl⟩

theorem W_of {k k' : ℕ} {h h' : ℤ} {A : Module.End ℂ M} (hk : k ≤ k') (hh : h = h') (hA : A ∈ W E k h) :
    A ∈ W E k' h' := hh ▸ Submodule.span_mono (fun _ hx => by obtain ⟨w, h1, h2, h3⟩ := hx; exact ⟨w, h1.trans hk, h2, h3⟩) hA

theorem W_ind {k : ℕ} {h : ℤ} {p : Module.End ℂ M → Prop} (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y))
    (hsm : ∀ (c : ℂ) x, p x → p (c • x)) (hw : ∀ w : List (Fin n × Fin n), w.length ≤ k → ht w = h → p (word E w))
    {A : Module.End ℂ M} (hA : A ∈ W E k h) : p A := by
  induction hA using Submodule.span_induction with
  | mem x hx => obtain ⟨w, h1, h2, rfl⟩ := hx; exact hw w h1 h2
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsm c x hx

theorem one_mem (k : ℕ) : (1 : Module.End ℂ M) ∈ W E k 0 :=
  word_mem E [] (Nat.zero_le _) (by simp [ht])

theorem letter_mem (a b : Fin n) : E a b ∈ W E 1 (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) := by
  have := word_mem E [(a, b)] le_rfl rfl
  simpa [word, ht] using this

theorem mul_mem {k k' : ℕ} {h h' : ℤ} {A B : Module.End ℂ M} (hA : A ∈ W E k h) (hB : B ∈ W E k' h') :
    A * B ∈ W E (k + k') (h + h') := by
  have key : ∀ w w' : List (Fin n × Fin n), w.length ≤ k → ht w = h → w'.length ≤ k' → ht w' = h' →
      word E w * word E w' ∈ W E (k + k') (h + h') := by
    intro w w' h1 h2 h3 h4
    have e : word E w * word E w' = word E (w ++ w') := by simp [word, List.prod_append]
    rw [e]
    refine word_mem E _ (by simp only [List.length_append]; omega) ?_
    rw [← h2, ← h4]; simp [ht, List.sum_append]
  refine W_ind E (p := fun A => A * B ∈ W E (k + k') (h + h')) (by simp)
    (fun x y hx hy => by rw [add_mul]; exact add_mem hx hy)
    (fun c x hx => by rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx) ?_ hA
  intro w h1 h2
  refine W_ind E (p := fun B => word E w * B ∈ W E (k + k') (h + h')) (by simp)
    (fun x y hx hy => by rw [mul_add]; exact add_mem hx hy)
    (fun c x hx => by rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx) ?_ hB
  intro w' h3 h4
  exact key w w' h1 h2 h3 h4

theorem comm_mem (hE : GlRel E) (a b : Fin n) {k : ℕ} {h : ℤ} {A : Module.End ℂ M} (hA : A ∈ W E k h) :
    E a b * A - A * E a b ∈ W E k (h + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ))) := by
  have gl : ∀ c e : Fin n, E a b * E c e - E c e * E a b ∈
      W E 1 ((((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) + (((e : ℕ) : ℤ) - ((c : ℕ) : ℤ))) := by
    intro c e
    rw [hE a b c e]
    refine sub_mem ?_ ?_
    · split_ifs with h1
      · subst h1; exact W_of E le_rfl (by ring) (letter_mem E a e)
      · exact zero_mem _
    · split_ifs with h1
      · subst h1; exact W_of E le_rfl (by ring) (letter_mem E c b)
      · exact zero_mem _
  have hw : ∀ w : List (Fin n × Fin n),
      E a b * word E w - word E w * E a b ∈ W E w.length (ht w + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ))) := by
    intro w
    induction w with
    | nil => simp [word]
    | cons y w ih =>
      rw [word_cons]
      have e1 : E a b * (E y.1 y.2 * word E w) - E y.1 y.2 * word E w * E a b =
          (E a b * E y.1 y.2 - E y.1 y.2 * E a b) * word E w +
            E y.1 y.2 * (E a b * word E w - word E w * E a b) := by noncomm_ring
      rw [e1]
      refine add_mem ?_ ?_
      · exact W_of E (by simp only [List.length_cons]; omega) (by rw [ht_cons]; ring)
          (mul_mem E (gl y.1 y.2) (word_mem E w le_rfl rfl))
      · exact W_of E (by simp only [List.length_cons]; omega) (by rw [ht_cons]; ring)
          (mul_mem E (letter_mem E y.1 y.2) ih)
  refine W_ind E (p := fun A => E a b * A - A * E a b ∈ W E k (h + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)))) (by simp) ?_ ?_ ?_ hA
  · intro x y hx hy
    have e : E a b * (x + y) - (x + y) * E a b = (E a b * x - x * E a b) + (E a b * y - y * E a b) := by
      noncomm_ring
    rw [e]; exact add_mem hx hy
  · intro c x hx
    have e : E a b * (c • x) - (c • x) * E a b = c • (E a b * x - x * E a b) := by
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    rw [e]; exact Submodule.smul_mem _ c hx
  · intro w h1 h2
    exact W_of E h1 (by rw [h2]) (hw w)

section wh
variable {ℓ : M →ₗ[ℂ] ℂ} {ψ : Fin n → Fin n → ℂ} (hE : GlRel E)
  (hψ2 : ∀ a b : Fin n, (a : ℕ) + 1 < b → ψ a b = 0) (hψ : ∀ a b : Fin n, a < b → ℓ ∘ₗ E a b = ψ a b • ℓ)
include hE hψ2 hψ

theorem letter_zero {k : ℕ} (hQ : ∀ (h : ℤ) (A : Module.End ℂ M), A ∈ W E k h → (k : ℤ) < h → ℓ ∘ₗ A = 0)
    (a b : Fin n) (hab : ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) ≤ 0) {h : ℤ} {A : Module.End ℂ M} (hA : A ∈ W E k h)
    (hk : (k : ℤ) < h + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ))) : ℓ ∘ₗ (E a b * A) = 0 := by
  have e : E a b * A = A * E a b + (E a b * A - A * E a b) := by abel
  rw [e, LinearMap.comp_add]
  have h1 : ℓ ∘ₗ (A * E a b) = 0 := by
    rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hQ h A hA (by linarith), LinearMap.zero_comp]
  rw [h1, hQ _ _ (comm_mem E hE a b hA) hk, add_zero]

theorem vanish (k : ℕ) : ∀ (h : ℤ) (A : Module.End ℂ M), A ∈ W E k h → (k : ℤ) < h → ℓ ∘ₗ A = 0 := by
  induction k with
  | zero =>
    intro h A hA hk
    refine W_ind E (p := fun A => ℓ ∘ₗ A = 0) (by simp)
      (fun x y hx hy => by rw [LinearMap.comp_add, hx, hy, add_zero])
      (fun c x hx => by rw [LinearMap.comp_smul, hx, smul_zero]) ?_ hA
    intro w h1 h2
    have : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [ht] at h2; omega
  | succ k ih =>
    intro h A hA hk
    refine W_ind E (p := fun A => ℓ ∘ₗ A = 0) (by simp)
      (fun x y hx hy => by rw [LinearMap.comp_add, hx, hy, add_zero])
      (fun c x hx => by rw [LinearMap.comp_smul, hx, smul_zero]) ?_ hA
    intro w h1 h2
    cases w with
    | nil => simp [ht] at h2; omega
    | cons x w =>
      obtain ⟨a, b⟩ := x
      rw [ht_cons] at h2
      simp only [List.length_cons] at h1
      rw [word_cons]
      have hw : word E w ∈ W E k (ht w) := word_mem E w (by omega) rfl
      rcases lt_or_ge a b with hab | hab
      · have hab' := Fin.lt_def.1 hab
        rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hψ a b hab]
        rcases (show (a : ℕ) + 1 = b ∨ (a : ℕ) + 1 < b by omega) with h3 | h3
        · rw [LinearMap.smul_comp, ih _ _ hw (by push_cast at hk h2 ⊢; omega), smul_zero]
        · rw [hψ2 a b h3, zero_smul, LinearMap.zero_comp]
      · have hab' := Fin.le_def.1 hab
        exact letter_zero E hE hψ2 hψ ih a b (by push_cast; omega) hw (by push_cast at hk h2 ⊢; omega)

theorem scalar (d : ℕ) : ∀ A : Module.End ℂ M, A ∈ W E d d → ∃ c : ℂ, ℓ ∘ₗ A = c • ℓ := by
  induction d with
  | zero =>
    intro A hA
    refine W_ind E (p := fun A => ∃ c : ℂ, ℓ ∘ₗ A = c • ℓ) ⟨0, by simp⟩ ?_ ?_ ?_ hA
    · rintro x y ⟨c, hc⟩ ⟨c', hc'⟩; exact ⟨c + c', by rw [LinearMap.comp_add, hc, hc', add_smul]⟩
    · rintro c x ⟨c', hc'⟩; exact ⟨c * c', by rw [LinearMap.comp_smul, hc', smul_smul]⟩
    · intro w h1 h2
      have : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      exact ⟨1, by simp only [word, List.map_nil, List.prod_nil, one_smul]; exact LinearMap.comp_id ℓ⟩
  | succ d ih =>
    intro A hA
    refine W_ind E (p := fun A => ∃ c : ℂ, ℓ ∘ₗ A = c • ℓ) ⟨0, by simp⟩ ?_ ?_ ?_ hA
    · rintro x y ⟨c, hc⟩ ⟨c', hc'⟩; exact ⟨c + c', by rw [LinearMap.comp_add, hc, hc', add_smul]⟩
    · rintro c x ⟨c', hc'⟩; exact ⟨c * c', by rw [LinearMap.comp_smul, hc', smul_smul]⟩
    · intro w h1 h2
      cases w with
      | nil => simp [ht] at h2; omega
      | cons x w =>
        obtain ⟨a, b⟩ := x
        rw [ht_cons] at h2
        simp only [List.length_cons] at h1
        rw [word_cons]
        rcases lt_or_ge a b with hab | hab
        · have hab' := Fin.lt_def.1 hab
          rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hψ a b hab]
          rcases (show (a : ℕ) + 1 = b ∨ (a : ℕ) + 1 < b by omega) with h3 | h3
          · obtain ⟨c, hc⟩ := ih _ (word_mem E w (by omega) (by push_cast at h2; omega))
            exact ⟨ψ a b * c, by rw [LinearMap.smul_comp, hc, smul_smul]⟩
          · exact ⟨0, by rw [hψ2 a b h3]; simp⟩
        · have hab' := Fin.le_def.1 hab
          exact ⟨0, by rw [letter_zero E hE hψ2 hψ (vanish E hE hψ2 hψ d) a b (by push_cast; omega)
            (word_mem E w (by omega) rfl) (by push_cast at h2 ⊢; omega), zero_smul]⟩

end wh

section eval
variable {P : Type} [Fintype P] [DecidableEq P]

theorem Om_single (p : P) (I : P → Fin n) (v : M) :
    Om E p (Pi.single I v : TV n M P) = ∑ c, Pi.single (Function.update I p c) (E (I p) c v) := by
  funext J
  rw [Om_apply, Finset.sum_apply]
  by_cases hJ : ∀ q, q ≠ p → J q = I q
  · rw [Finset.sum_eq_single_of_mem (I p) (Finset.mem_univ _) ?_,
      Finset.sum_eq_single_of_mem (J p) (Finset.mem_univ _) ?_]
    · have h1 : Function.update J p (I p) = I := by
        funext q; by_cases hq : q = p
        · subst hq; simp
        · rw [Function.update_of_ne hq]; exact hJ q hq
      have h2 : J = Function.update I p (J p) := by
        funext q; by_cases hq : q = p
        · subst hq; simp
        · rw [Function.update_of_ne hq]; exact hJ q hq
      rw [h1, Pi.single_eq_same, ← h2, Pi.single_eq_same]
    · intro c _ hc
      rw [Pi.single_eq_of_ne]
      intro h; apply hc; rw [h]; simp
    · intro a _ ha
      rw [Pi.single_eq_of_ne, map_zero]
      intro h; apply ha; rw [← h]; simp
  · push_neg at hJ
    obtain ⟨q, hq, hne⟩ := hJ
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro c _; rw [Pi.single_eq_of_ne]; intro h; apply hne; rw [h, Function.update_of_ne hq]
    · intro a _; rw [Pi.single_eq_of_ne, map_zero]; intro h; apply hne; rw [← h, Function.update_of_ne hq]

theorem pm_single (σ : Equiv.Perm P) (I : P → Fin n) (v : M) :
    pm σ (Pi.single I v : TV n M P) = Pi.single (I ∘ σ.symm) v := by
  funext J
  rw [pm_apply]
  simp only [Pi.single_apply, Equiv.eq_comp_symm]

def H (J I : P → Fin n) : ℤ := ∑ p, (((J p : ℕ) : ℤ) - ((I p : ℕ) : ℤ))

theorem eval {d : ℕ} {g : Module.End ℂ (TV n M P)} (hg : Deg E d g) (J : P → Fin n) :
    ∀ I : P → Fin n, ∃ A ∈ W E d (H J I), ∀ v, g (Pi.single I v) J = A v := by
  induction hg with
  | one d =>
    intro I
    by_cases h : J = I
    · subst h; exact ⟨1, W_of E le_rfl (by simp [H]) (one_mem E d), fun v => by simp⟩
    · exact ⟨0, zero_mem _, fun v => by simp [Pi.single_eq_of_ne h]⟩
  | add _ _ ih1 ih2 =>
    intro I
    obtain ⟨A, hA, hAv⟩ := ih1 I
    obtain ⟨B, hB, hBv⟩ := ih2 I
    exact ⟨A + B, add_mem hA hB, fun v => by simp [hAv, hBv]⟩
  | smul c _ ih =>
    intro I
    obtain ⟨A, hA, hAv⟩ := ih I
    exact ⟨c • A, Submodule.smul_mem _ c hA, fun v => by simp [hAv]⟩
  | om p _ ih =>
    intro I
    choose A hA hAv using fun c => ih (Function.update I p c)
    refine ⟨∑ c, A c * E (I p) c, Submodule.sum_mem _ fun c _ => ?_, fun v => ?_⟩
    · refine W_of E le_rfl ?_ (mul_mem E (hA c) (letter_mem E (I p) c))
      have : H J (Function.update I p c) - H J I = ((I p : ℕ) : ℤ) - ((c : ℕ) : ℤ) := by
        simp only [H, ← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_single p]
        · simp
        · intro q _ hq; simp [Function.update_of_ne hq]
        · simp
      linarith
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [Module.End.mul_apply, Om_single, map_sum, Finset.sum_apply, LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun c _ => by rw [hAv]; rfl
  | perm σ _ ih =>
    intro I
    obtain ⟨A, hA, hAv⟩ := ih (I ∘ σ.symm)
    refine ⟨A, W_of E le_rfl ?_ hA, fun v => ?_⟩
    · simp only [H, Finset.sum_sub_distrib, Function.comp_apply]
      rw [Equiv.sum_comp σ.symm (fun p => ((I p : ℕ) : ℤ))]
    · rw [Module.End.mul_apply, pm_single, hAv]

theorem deg_succ {d : ℕ} {g : Module.End ℂ (TV n M P)} (hg : Deg E d g) : Deg E (d + 1) g := by
  induction hg with
  | one d => exact Deg.one _
  | add _ _ ih1 ih2 => exact Deg.add ih1 ih2
  | smul c _ ih => exact Deg.smul c ih
  | om p _ ih => exact Deg.om p ih
  | perm σ _ ih => exact Deg.perm σ ih

end eval

theorem prod_deg (L : List ℂ) :
    Deg E L.length (L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod ∧
      Commute (Om E (0 : Fin 1)) (L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod := by
  induction L with
  | nil => exact ⟨Deg.one 0, Commute.one_right _⟩
  | cons r L ih =>
    obtain ⟨h1, h2⟩ := ih
    have hc : Commute (Om E (0 : Fin 1)) (Om E 0 - algebraMap ℂ _ r) :=
      (Commute.refl _).sub_right (show Commute (algebraMap ℂ _ r) (Om E (0 : Fin 1)) from Algebra.commutes r _).symm
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    refine ⟨?_, hc.mul_right h2⟩
    rw [sub_mul, h2.eq, ← Algebra.smul_def, sub_eq_add_neg, ← neg_smul]
    exact Deg.add (Deg.om 0 h1) (Deg.smul (-r) (deg_succ E h1))

theorem prod_exact {ℓ : M →ₗ[ℂ] ℂ} {ψ : Fin n → Fin n → ℂ} (hE : GlRel E)
    (hψ1 : ∀ a b : Fin n, (a : ℕ) + 1 = b → ψ a b ≠ 0)
    (hψ2 : ∀ a b : Fin n, (a : ℕ) + 1 < b → ψ a b = 0) (hψ : ∀ a b : Fin n, a < b → ℓ ∘ₗ E a b = ψ a b • ℓ)
    (L : List ℂ) : ∀ j i : Fin n, (j : ℕ) + L.length = i → ∃ c : ℂ, c ≠ 0 ∧ ∀ v,
      ℓ ((L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod (Pi.single (fun _ => j) v) (fun _ => i)) =
        c * ℓ v := by
  have hl : ∀ (b c : Fin n) (X : M), b < c → ℓ (E b c X) = ψ b c * ℓ X := fun b c X hbc => by
    rw [← LinearMap.comp_apply, hψ b c hbc]; rfl
  have hu : ∀ b : Fin n, Function.update (fun _ : Fin 1 => b) 0 = fun c => (fun _ : Fin 1 => c) := by
    intro b; funext c x; rw [Subsingleton.elim x 0]; simp
  induction L with
  | nil =>
    intro j i hji
    have : j = i := Fin.ext (by simpa using hji)
    subst this
    exact ⟨1, one_ne_zero, fun v => by simp⟩
  | cons r L ih =>
    intro j i hji
    simp only [List.length_cons] at hji
    obtain ⟨hdeg, -⟩ := prod_deg E L
    set a : Fin n := ⟨(i : ℕ) - 1, by omega⟩ with ha
    obtain ⟨c, hc, hcv⟩ := ih j a (by simp only [a]; omega)
    refine ⟨ψ a i * c, mul_ne_zero (hψ1 a i (by simp only [a]; omega)) hc, fun v => ?_⟩
    simp only [List.map_cons, List.prod_cons]
    rw [Module.End.mul_apply, LinearMap.sub_apply, Pi.sub_apply, map_sub]
    obtain ⟨B, hB, hBv⟩ := eval E hdeg (fun _ => i) (fun _ => j)
    have h2 : ℓ (algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) r ((L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod
        (Pi.single (fun _ => j) v)) (fun _ => i)) = 0 := by
      rw [Module.algebraMap_end_apply, Pi.smul_apply, hBv, map_smul, ← LinearMap.comp_apply,
        vanish E hE hψ2 hψ L.length _ B hB (by simp [H]; omega)]
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, sub_zero, Om_apply, map_sum, hu]
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _) ?_]
    · rw [hl a i _ (Fin.lt_def.2 (by simp only [a]; omega)), hcv]; ring
    · intro a' _ ha'
      rcases lt_or_ge a' i with h3 | h3
      · have h3' := Fin.lt_def.1 h3
        have h4 : (a' : ℕ) + 1 < i := by
          rcases (show (a' : ℕ) + 1 < i ∨ (a' : ℕ) = (i : ℕ) - 1 by omega) with h | h
          · exact h
          · exact absurd (Fin.ext (by simp only [a]; omega)) ha'
        rw [hl a' i _ h3, hψ2 a' i h4, zero_mul]
      · have h3' := Fin.le_def.1 h3
        obtain ⟨B', hB', hB'v⟩ := eval E hdeg (fun _ => a') (fun _ => j)
        rw [hB'v, ← Module.End.mul_apply, ← LinearMap.comp_apply,
          letter_zero E hE hψ2 hψ (vanish E hE hψ2 hψ L.length) a' i (by push_cast; omega) hB'
            (by simp [H]; omega)]
        rfl

end HeightVanishing

open HeightVanishing in
theorem height_of : TensorGl → Height := by
  intro _ n M _ _ E hE ℓ hW top htop
  obtain ⟨ψ, hψ1, hψ2, hψ⟩ := hW
  have hcast : ∀ {P : Type} [Fintype P] (I : P → Fin n),
      ((∑ p, ((top : ℕ) - I p) : ℕ) : ℤ) = H (fun _ => top) I := by
    intro P _ I
    simp only [H]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.cast_sub (by omega)]
  refine ⟨fun P _ _ d g hg I => ⟨fun hd v => ?_, fun hd => ?_⟩, fun hl L hL => ?_, fun m => ?_⟩
  · obtain ⟨A, hA, hAv⟩ := eval E hg (fun _ => top) I
    rw [hAv, ← LinearMap.comp_apply, vanish E hE hψ2 hψ d _ A hA (by rw [← hcast]; exact_mod_cast hd)]
    rfl
  · obtain ⟨A, hA, hAv⟩ := eval E hg (fun _ => top) I
    obtain ⟨c, hc⟩ := scalar E hE hψ2 hψ d A (W_of E le_rfl (by rw [← hcast, hd]) hA)
    exact ⟨c, fun v => by rw [hAv, ← LinearMap.comp_apply, hc]; rfl⟩
  · have h0 : 0 < n := by omega
    obtain ⟨c, hc, hcv⟩ := prod_exact E hE hψ1 hψ2 hψ L ⟨0, h0⟩ top (by simp [hL])
    obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
      by_contra h; push_neg at h; exact hl (LinearMap.ext h)
    intro h
    have := LinearMap.congr_fun h (Pi.single (fun _ => ⟨0, h0⟩) v)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.zero_apply] at this
    rw [hcv] at this
    exact mul_ne_zero hc hv this
  · refine ⟨ψ, hψ1, hψ2, fun a b hab => ?_⟩
    have hab' := Fin.lt_def.1 hab
    have hta : top ≠ a := by
      intro h; subst h; have := b.2; omega
    ext f
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smul_apply]
    rw [tE_apply]
    simp only [hta, if_false, Finset.sum_const_zero, add_zero]
    rw [← LinearMap.comp_apply, hψ a b hab]
    rfl

end PositivityTheory.Rg.Cz

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSpectrum
noncomputable section

open Formalism.REAL

namespace PositivityTheory.Rg.Cz

namespace SpecA

variable {n : ℕ}

def Kl {V : Type} [AddCommGroup V] [Module ℂ V] (X : Module.End ℂ V) (s : ℂ) : Prop :=
  ∃ L : List ℕ, (L.map fun r : ℕ => X - algebraMap ℂ _ (s + r)).prod = 0

theorem prodL_nat {ι V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : V →ₗ[ℂ] W) (A : Module.End ℂ V) (B : Module.End ℂ W) (h : Φ ∘ₗ A = B ∘ₗ Φ) (g : ι → ℂ) (L : List ι) :
    Φ ∘ₗ (L.map fun r => A - algebraMap ℂ _ (g r)).prod = (L.map fun r => B - algebraMap ℂ _ (g r)).prod ∘ₗ Φ := by
  induction L with
  | nil =>
    ext v
    simp
  | cons r L ih =>
    have key : Φ ∘ₗ (A - algebraMap ℂ _ (g r)) = (B - algebraMap ℂ _ (g r)) ∘ₗ Φ := by
      ext v
      have hv := LinearMap.congr_fun h v
      simp only [LinearMap.comp_apply] at hv
      simp [hv]
    simp only [List.map_cons, List.prod_cons]
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, key,
      LinearMap.comp_assoc, ih, LinearMap.comp_assoc]

theorem Kl_nat {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : V →ₗ[ℂ] W) (hΦ : Function.Injective Φ) (A : Module.End ℂ V) (B : Module.End ℂ W) (h : Φ ∘ₗ A = B ∘ₗ Φ)
    (s : ℂ) (hB : Kl B s) : Kl A s := by
  obtain ⟨L, hL⟩ := hB
  refine ⟨L, ?_⟩
  have hP := prodL_nat Φ A B h (fun r : ℕ => s + (r : ℂ)) L
  rw [hL, LinearMap.zero_comp] at hP
  ext v
  apply hΦ
  rw [LinearMap.zero_apply, map_zero]
  simpa using LinearMap.congr_fun hP v

theorem Kl_lift {V P : Type} [AddCommGroup V] [Module ℂ V] (X : Module.End ℂ V) (s : ℂ) (h : Kl X s) :
    Kl (lift X : Module.End ℂ (TV n V P)) s := by
  obtain ⟨L, hL⟩ := h
  refine ⟨L, ?_⟩
  refine LinearMap.ext fun f => funext fun I => ?_
  have hc : (LinearMap.proj I : TV n V P →ₗ[ℂ] V) ∘ₗ lift X = X ∘ₗ LinearMap.proj I :=
    LinearMap.ext fun f => rfl
  have hP := prodL_nat (LinearMap.proj I) (lift X) X hc (fun r : ℕ => s + (r : ℂ)) L
  rw [hL, LinearMap.zero_comp] at hP
  simpa using LinearMap.congr_fun hP f

theorem dvd_prod_shift_sub_prod {R : Type*} [CommRing R] (Y : R) (Z : List R) : Y ∣ (Z.map (Y + ·)).prod - Z.prod := by
  induction Z with
  | nil => simp
  | cons z Z ih =>
    simp only [List.map_cons, List.prod_cons]
    have he : (Y + z) * (Z.map (Y + ·)).prod - z * Z.prod =
        Y * (Z.map (Y + ·)).prod + z * ((Z.map (Y + ·)).prod - Z.prod) := by ring
    rw [he]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right ih _)

theorem sum_comm {R : Type*} [CommRing R] [Algebra ℂ R] (A B : R) (α β : ℂ) (La Lb : List ℕ)
    (hA : (La.map fun a : ℕ => A - algebraMap ℂ R (α + a)).prod = 0)
    (hB : (Lb.map fun b : ℕ => B - algebraMap ℂ R (β + b)).prod = 0) :
    ((La.flatMap fun a => Lb.map (a + ·)).map fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)).prod = 0 := by
  set x : ℕ → R := fun a => A - algebraMap ℂ R (α + a) with hx
  set y : ℕ → R := fun b => B - algebraMap ℂ R (β + b) with hy
  have hA' : (La.map x).prod = 0 := hA
  have hB' : (Lb.map y).prod = 0 := hB
  have hterm : ∀ a b : ℕ, A + B - algebraMap ℂ R (α + β + ((a + b : ℕ) : ℂ)) = x a + y b := by
    intro a b
    simp only [hx, hy]
    push_cast
    ring
  have key : ∀ L : List ℕ, ∃ u v : R,
      ((L.flatMap fun a => Lb.map (a + ·)).map fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)).prod =
        u * (L.map x).prod + v * (Lb.map y).prod := by
    intro L
    induction L with
    | nil => exact ⟨1, 0, by simp⟩
    | cons a L ih =>
      obtain ⟨u, v, huv⟩ := ih
      obtain ⟨c, hc⟩ := dvd_prod_shift_sub_prod (x a) (Lb.map y)
      have h1 : ((Lb.map (a + ·)).map fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)).prod =
          x a * c + (Lb.map y).prod := by
        rw [← hc, List.map_map, List.map_map]
        have hm : ((fun c : ℕ => A + B - algebraMap ℂ R (α + β + c)) ∘ (a + ·)) =
            ((x a + ·) ∘ y) := by
          funext b
          exact hterm a b
        rw [hm]
        ring
      refine ⟨c * u, (x a * c + (Lb.map y).prod) * v + u * (L.map x).prod, ?_⟩
      rw [List.flatMap_cons, List.map_append, List.prod_append, huv, h1]
      simp only [List.map_cons, List.prod_cons]
      ring
  obtain ⟨u, v, huv⟩ := key La
  rw [huv, hA', hB']
  ring

theorem Kl_sum {V : Type} [AddCommGroup V] [Module ℂ V] (A B : Module.End ℂ V) (hAB : Commute A B) (α β : ℂ)
    (hA : Kl A α) (hB : Kl B β) : Kl (A + B) (α + β) := by
  obtain ⟨La, hLa⟩ := hA
  obtain ⟨Lb, hLb⟩ := hB
  refine ⟨La.flatMap fun a => Lb.map (a + ·), ?_⟩
  have hc : ∀ a ∈ ({A, B} : Set (Module.End ℂ V)), ∀ b ∈ ({A, B} : Set (Module.End ℂ V)), a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hAB.eq
    · exact hAB.eq.symm
    · rfl
  open scoped IsMulCommutative in
  letI : IsMulCommutative (Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V))) :=
    Algebra.isMulCommutative_adjoin ℂ (fun a ha b hb _ => hc a ha b hb)
  let a' : Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V)) := ⟨A, Algebra.subset_adjoin (by simp)⟩
  let b' : Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V)) := ⟨B, Algebra.subset_adjoin (by simp)⟩
  have hinj : Function.Injective (Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V))).val := Subtype.val_injective
  have hA' : (La.map fun a : ℕ => a' - algebraMap ℂ _ (α + a)).prod = 0 := by
    apply hinj
    rw [map_list_prod, map_zero, List.map_map]
    set_option synthInstance.maxHeartbeats 200000 in
      simpa [Function.comp_def, a'] using hLa
  have hB' : (Lb.map fun b : ℕ => b' - algebraMap ℂ _ (β + b)).prod = 0 := by
    apply hinj
    rw [map_list_prod, map_zero, List.map_map]
    set_option synthInstance.maxHeartbeats 200000 in
      simpa [Function.comp_def, b'] using hLb
  have hs := congrArg (Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V))).val (sum_comm a' b' α β La Lb hA' hB')
  rw [map_list_prod, map_zero, List.map_map] at hs
  set_option synthInstance.maxHeartbeats 200000 in
    simpa [Function.comp_def, a', b'] using hs

theorem xJ_apply {m : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m)
    (f : TV n M (Fin m)) (I : Fin m → Fin n) :
    xJ E j f I = ∑ a, E a (I j) (f (Function.update I j a)) +
      ∑ i ∈ Finset.univ.filter (· < j), f (I ∘ Equiv.swap i j) := by
  simp [xJ, Om, lift, eAt, pm, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (I j)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem xJ_nat {m : ℕ} {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    (E₁ : Fin n → Fin n → Module.End ℂ M₁) (E₂ : Fin n → Fin n → Module.End ℂ M₂) (φ : M₁ →ₗ[ℂ] M₂)
    (h : ∀ a b, φ ∘ₗ E₁ a b = E₂ a b ∘ₗ φ) (j : Fin m) :
    LinearMap.compLeft φ (Fin m → Fin n) ∘ₗ xJ E₁ j = xJ E₂ j ∘ₗ LinearMap.compLeft φ (Fin m → Fin n) := by
  have h' : ∀ a b v, φ (E₁ a b v) = E₂ a b (φ v) := fun a b v => LinearMap.congr_fun (h a b) v
  refine LinearMap.ext fun f => funext fun I => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp [xJ_apply, map_add (f := _), map_sum, h', LinearMap.compLeft_apply]

theorem glrel_inj {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (G : Fin n → Fin n → Module.End ℂ V) (H : Fin n → Fin n → Module.End ℂ W) (φ : V →ₗ[ℂ] W)
    (hφ : Function.Injective φ) (h : ∀ a b, φ ∘ₗ G a b = H a b ∘ₗ φ) (hH : GlRel H) : GlRel G := by
  have h' : ∀ a b v, φ (G a b v) = H a b (φ v) := fun a b v => LinearMap.congr_fun (h a b) v
  intro a b c d
  ext v
  apply hφ
  have hv := LinearMap.congr_fun (hH a b c d) (φ v)
  by_cases hbc : b = c <;> by_cases hda : d = a <;> simpa [h', hbc, hda] using hv

theorem ker_stable {V : Type} [AddCommGroup V] [Module ℂ V] (Y X : Module.End ℂ V) (h : Commute Y X) :
    ∀ w ∈ LinearMap.ker Y, X w ∈ LinearMap.ker Y := by
  intro w hw
  rw [LinearMap.mem_ker] at hw ⊢
  rw [← Module.End.mul_apply, h.eq, Module.End.mul_apply, hw, map_zero]

theorem comm_prod {V : Type} [AddCommGroup V] [Module ℂ V] (A X : Module.End ℂ V) (h : Commute A X)
    {ι : Type} (g : ι → ℂ) (L : List ι) : Commute (L.map fun c => A - algebraMap ℂ _ (g c)).prod X := by
  refine Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  exact h.sub_left (Algebra.commute_algebraMap_left _ _)

theorem filt {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (G : Fin n → Fin n → Module.End ℂ V)
    (A : Module.End ℂ V) (hG : GlRel G) (hGA : ∀ a b, Commute A (G a b)) (l : Fin n → ℂ) (s : ℂ) (j : Fin k)
    (H : ∀ (W : Submodule ℂ V) (hW : ∀ a b, ∀ w ∈ W, G a b w ∈ W) (hA : ∀ w ∈ W, A w ∈ W) (c : Fin n)
      (N : Type) [AddCommGroup N] [Module ℂ N] (F : Fin n → Fin n → Module.End ℂ N) (q : W →ₗ[ℂ] N),
      GlRel F → Function.Surjective q → (∀ a b (w : W), q ⟨_, hW a b w w.2⟩ = F a b (q w)) →
      (∀ w : W, q ⟨_, hA w w.2⟩ = l c • q w) → Kl (xJ F j) s)
    (ks : List (Fin n)) : ∃ L : List ℕ, ∀ f : TV n V (Fin k),
      (∀ I, (ks.map fun c => A - algebraMap ℂ _ (l c)).prod (f I) = 0) →
      (L.map fun r : ℕ => xJ G j - algebraMap ℂ _ (s + r)).prod f = 0 := by
  induction ks with
  | nil =>
    refine ⟨[], fun f hf => ?_⟩
    have hf0 : f = 0 := funext fun I => by simpa using hf I
    simp [hf0]
  | cons c ks ih =>
    obtain ⟨L2, hL2⟩ := ih
    set Y : Module.End ℂ V := (ks.map fun c => A - algebraMap ℂ _ (l c)).prod with hYdef
    set Z : Module.End ℂ V := A - algebraMap ℂ _ (l c) with hZ
    have hZG : ∀ a b, Commute Z (G a b) := fun a b =>
      (hGA a b).sub_left (Algebra.commute_algebraMap_left _ _)
    have hZA : Commute Z A := (Commute.refl A).sub_left (Algebra.commute_algebraMap_left _ _)
    have hW : ∀ a b, ∀ w ∈ LinearMap.ker Z, G a b w ∈ LinearMap.ker Z :=
      fun a b => ker_stable Z (G a b) (hZG a b)
    have hWA : ∀ w ∈ LinearMap.ker Z, A w ∈ LinearMap.ker Z := ker_stable Z A hZA
    let F : Fin n → Fin n → Module.End ℂ (LinearMap.ker Z) := fun a b =>
      LinearMap.codRestrict (LinearMap.ker Z) ((G a b).comp (LinearMap.ker Z).subtype) (fun w => hW a b w w.2)
    have hsub : ∀ a b, (LinearMap.ker Z).subtype ∘ₗ F a b = G a b ∘ₗ (LinearMap.ker Z).subtype :=
      fun a b => LinearMap.ext fun w => rfl
    have hF : GlRel F := glrel_inj F G (LinearMap.ker Z).subtype (LinearMap.ker Z).injective_subtype hsub hG
    have hKl := H (LinearMap.ker Z) hW hWA c (LinearMap.ker Z) F LinearMap.id hF Function.surjective_id
      (fun a b w => rfl) (fun w => by
        apply Subtype.ext
        have hw : (A - algebraMap ℂ (Module.End ℂ V) (l c)) (w : V) = 0 := LinearMap.mem_ker.1 w.2
        rw [LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at hw
        simpa using hw)
    obtain ⟨L1, hL1⟩ := hKl
    have hΦ := prodL_nat (LinearMap.compLeft (LinearMap.ker Z).subtype (Fin k → Fin n)) (xJ F j) (xJ G j)
      (xJ_nat F G (LinearMap.ker Z).subtype hsub j) (fun r : ℕ => s + (r : ℂ)) L1
    rw [hL1, LinearMap.comp_zero] at hΦ
    have hYG : ∀ a b, Y ∘ₗ G a b = G a b ∘ₗ Y := fun a b => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
      exact (comm_prod A (G a b) (hGA a b) l ks).eq
    have hΨ := prodL_nat (LinearMap.compLeft Y (Fin k → Fin n)) (xJ G j) (xJ G j) (xJ_nat G G Y hYG j)
      (fun r : ℕ => s + (r : ℂ)) L1
    refine ⟨L2 ++ L1, fun f hf => ?_⟩
    rw [List.map_append, List.prod_append, Module.End.mul_apply]
    apply hL2
    intro I
    have hf' : ∀ I, Y (f I) ∈ LinearMap.ker Z := fun I => by
      have hI := hf I
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply] at hI
      exact LinearMap.mem_ker.2 hI
    have h0 := LinearMap.congr_fun hΦ (fun I => (⟨Y (f I), hf' I⟩ : LinearMap.ker Z))
    have h1 := LinearMap.congr_fun hΨ f
    rw [LinearMap.comp_apply] at h0 h1
    rw [LinearMap.comp_apply] at h1
    have h2 : (LinearMap.compLeft (LinearMap.ker Z).subtype (Fin k → Fin n))
        (fun I => (⟨Y (f I), hf' I⟩ : LinearMap.ker Z)) = (LinearMap.compLeft Y (Fin k → Fin n)) f := rfl
    rw [h2, ← h1] at h0
    have h3 := congrFun h0.symm I
    simpa using h3

def Cl (k : ℕ) : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
  GlRel E → ∀ (l : Fin n → ℂ) (s : ℂ), HasChar E l → (∀ k, ∃ r : ℕ, l k = s + r) → ∀ j : Fin k, Kl (xJ E j) s

theorem cl_step (h1 : TensorGl) (h3 : Curry) (h5 : StepChar) (k : ℕ) (ih : Cl k) : Cl (1 + k) := by
  intro n M _ _ E hE l s hl hls j
  obtain ⟨hbij, -, hcast, hnat, -, -, -⟩ := h3 n M E 1 k
  obtain ⟨hstep1, hstep2⟩ := h5 n M E hE l hl
  choose r hr using hls
  induction j using Fin.addCases with
  | left i =>
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    apply Kl_nat (curF n M 1 k) hbij.1 _ _ (hcast 0)
    apply Kl_lift
    refine ⟨List.ofFn r, ?_⟩
    have hx : xJ E (0 : Fin 1) = Om E 0 := by simp [xJ]
    have he : (List.ofFn r).map (fun r : ℕ => Om E 0 - algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) (s + r)) =
        List.ofFn fun c => Om E 0 - algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) (l c) := by
      rw [List.map_ofFn]
      congr 1
      funext c
      simp [hr c]
    rw [hx, he]
    exact hstep1
  | right j' =>
    apply Kl_nat (curF n M 1 k) hbij.1 _ _ (hnat j')
    obtain ⟨hG, hGA, -, -⟩ := h1 n M (Fin 1) E hE Finset.univ
    have hls' : ∀ c c', ∃ r' : ℕ, Function.update l c (l c + 1) c' = s + r' := by
      intro c c'
      by_cases hcc : c' = c
      · subst hcc
        refine ⟨r c' + 1, ?_⟩
        simp [hr c']
        ring
      · exact ⟨r c', by simp [hcc, hr c']⟩
    obtain ⟨L, hL⟩ := filt (tE Finset.univ E) (Om E 0) hG (fun a b => hGA 0 (Finset.mem_univ _) a b) l s j'
      (by
        intro W hW hA c N _ _ F q hF hq hFq hAq
        exact ih n N F hF (Function.update l c (l c + 1)) s (hstep2 W N F q hW hA c hq hFq hAq) (hls' c) j')
      (List.finRange n)
    have h0 : ((List.finRange n).map fun c => Om E 0 - algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) (l c)).prod = 0 := by
      rw [← List.ofFn_eq_map]
      exact hstep1
    refine ⟨L, LinearMap.ext fun f => ?_⟩
    rw [LinearMap.zero_apply]
    exact hL f (fun I => by rw [h0]; rfl)

theorem cl_all (h1 : TensorGl) (h3 : Curry) (h5 : StepChar) : ∀ m, Cl m := by
  intro m
  induction m with
  | zero =>
    intro n M _ _ E hE l s hl hls j
    exact j.elim0
  | succ m ih =>
    rw [Nat.add_comm]
    exact cl_step h1 h3 h5 m ih

end SpecA

theorem spectrum_of : TensorGl → JMComm → Curry → StepChar → Spectrum := by
  intro h1 h2 h3 h5 n M _ _ E hE l s hl hls m
  have hcl : ∀ j : Fin m, SpecA.Kl (xJ E j) s := SpecA.cl_all h1 h3 h5 m n M E hE l s hl hls
  have hcomm := (h2 n M E hE m).1
  have hsum : ∀ k, k ≤ m →
      SpecA.Kl (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), xJ E j) ((k : ℂ) * s) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[0], ?_⟩
      simp
    | succ k ihk =>
      intro hk
      have hk' : k < m := hk
      have hfil : (Finset.univ.filter fun j : Fin m => (j : ℕ) < k + 1) =
          insert ⟨k, hk'⟩ (Finset.univ.filter fun j : Fin m => (j : ℕ) < k) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      have hsplit : (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k + 1), xJ E j) =
          (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), xJ E j) + xJ E ⟨k, hk'⟩ := by
        rw [hfil, Finset.sum_insert (by simp), add_comm]
      rw [hsplit, show ((k + 1 : ℕ) : ℂ) * s = (k : ℂ) * s + s by push_cast; ring]
      exact SpecA.Kl_sum _ _ (Commute.sum_left _ _ _ fun j _ => hcomm j ⟨k, hk'⟩) _ _ (ihk (by omega)) (hcl ⟨k, hk'⟩)
  exact ⟨fun k hk => hsum k hk, hcl⟩

end PositivityTheory.Rg.Cz

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PWallQuot
noncomputable section

open Formalism.REAL

namespace PositivityTheory.Rg.Cz

namespace WQ

section Alg

variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

theorem qdet_map (f : A →ₐ[ℂ] B) {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) :
    f (qdet E u) = qdet (fun a b => f (E a b)) u := by
  unfold qdet qminor
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
  simp only [Function.comp, Tm, map_add (f := _), apply_ite f, map_zero, AlgHom.commutes]

theorem glRel_map (f : A →ₐ[ℂ] B) {n : ℕ} {E : Fin n → Fin n → A} (h : GlRel E) : GlRel fun a b => f (E a b) := by
  intro a b c d
  have := congrArg f (h a b c d)
  simpa [map_sub, map_mul, apply_ite f] using this

theorem glRel_of_inj (f : A →ₐ[ℂ] B) (hf : Function.Injective f) {n : ℕ} {E : Fin n → Fin n → A}
    (h : GlRel fun a b => f (E a b)) : GlRel E := by
  intro a b c d
  apply hf
  simpa [map_sub, map_mul, apply_ite f] using h a b c d

theorem comm_qdet {n : ℕ} (E : Fin n → Fin n → A) (x : A) (h : ∀ a b, Commute x (E a b)) (u : ℂ) :
    Commute x (qdet E u) := by
  unfold qdet qminor
  refine Commute.sum_right _ _ _ fun σ _ => ?_
  refine Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
  unfold Tm
  refine Commute.add_right ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_right _ _
  · exact Commute.zero_right _

end Alg

section Quot

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stab (N : Submodule ℂ M) : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {X | ∀ y ∈ N, X y ∈ N}
  mul_mem' hX hY y hy := hX _ (hY y hy)
  add_mem' hX hY y hy := N.add_mem (hX y hy) (hY y hy)
  algebraMap_mem' c y hy := by simpa [Module.algebraMap_end_apply] using N.smul_mem c hy

def qmap (N : Submodule ℂ M) : stab N →ₐ[ℂ] Module.End ℂ (M ⧸ N) where
  toFun X := N.mapQ N X.1 (fun y hy => X.2 y hy)
  map_one' := by ext y; simp
  map_mul' X Y := by ext y; simp
  map_zero' := by ext y; simp
  map_add' X Y := by ext y; simp
  commutes' c := by ext y; simp [Module.algebraMap_end_apply]

end Quot

end WQ

open WQ

theorem wallQuot_of (hQ : QdetFacts) : WallQuot := by
  intro n M _ _ ι E hgl hcomm l φ hφ
  let N : Submodule ℂ M :=
    { carrier := {y | ∀ w ∈ envAlg E, φ (w y) = 0}
      add_mem' := fun {x y} hx hy w hw => by
        show φ (w (x + y)) = 0
        rw [map_add (f := _), map_add (f := _), hx w hw, hy w hw, add_zero]
      zero_mem' := fun w _ => by simp
      smul_mem' := fun c y hy w hw => by
        show φ (w (c • y)) = 0
        rw [map_smul, map_smul, hy w hw, smul_zero] }
  have hgen : ∀ τ a b, E τ a b ∈ envAlg E := fun τ a b => Algebra.subset_adjoin ⟨τ, a, b, rfl⟩
  have hstab : ∀ τ a b, E τ a b ∈ stab N := fun τ a b y hy w hw =>
    hy (w * E τ a b) (Subalgebra.mul_mem _ hw (hgen τ a b))
  let E' : ι → Fin n → Fin n → stab N := fun τ a b => ⟨E τ a b, hstab τ a b⟩
  let F : ι → Fin n → Fin n → Module.End ℂ (M ⧸ N) := fun τ a b => qmap N (E' τ a b)
  have hgl' : ∀ τ, GlRel (E' τ) := fun τ => glRel_of_inj (stab N).val Subtype.val_injective (hgl τ)
  have hcent : ∀ τ (u : ℂ), ∀ w ∈ envAlg E, Commute w (qdet (E τ) u) := by
    intro τ u w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨τ', a, b, rfl⟩ := hx
      by_cases h : τ' = τ
      · subst h
        exact ((hQ n M (E τ') (hgl τ')).1 u a b).symm
      · exact comm_qdet _ _ (fun c d => hcomm τ' τ h a b c d) u
    | algebraMap c => exact Algebra.commute_algebraMap_left _ _
    | add x y _ _ hx hy => exact hx.add_left hy
    | mul x y _ _ hx hy => exact hx.mul_left hy
  have hq : ∀ τ (u : ℂ) y, qdet (F τ) u (N.mkQ y) = N.mkQ (qdet (E τ) u y) := by
    intro τ u y
    rw [show qdet (F τ) u = qmap N (qdet (E' τ) u) from (qdet_map _ _ _).symm,
      show qdet (E τ) u = (stab N).val (qdet (E' τ) u) from (qdet_map (stab N).val (E' τ) u).symm]
    rfl
  refine ⟨N, F, fun τ => glRel_map (qmap N) (hgl' τ), fun τ τ' h a b c d => ?_, fun τ u => ?_,
    fun τ a b => LinearMap.ext fun y => rfl, fun y => Iff.rfl⟩
  · exact (show Commute (E' τ a b) (E' τ' c d) from Subtype.ext (hcomm τ τ' h a b c d).eq).map (qmap N)
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hq, Module.algebraMap_end_apply, ← N.mkQ.map_smul,
      Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    intro w hw
    show φ (w (qdet (E τ) u y - (∏ k, (u + l τ k)) • y)) = 0
    have hc := congrArg (fun T : Module.End ℂ M => φ (T y)) (hcent τ u w hw).eq
    simp only [Module.End.mul_apply] at hc
    have h2 := LinearMap.congr_fun (hφ τ u) (w y)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h2
    rw [map_sub, map_sub, map_smul, map_smul, hc, h2, sub_self]

end PositivityTheory.Rg.Cz

end
end

namespace PositivityTheory.Rg.Cz

theorem kType_holds : KType := by
  have tg := tensorGl_holds
  have jm := jmComm_of tg
  have cu := curry_holds
  have qd := qdetFacts_holds
  have pq := piQdet_of tg jm
  have sf := stepFormula_of tg jm pq cu
  have sc := stepChar_of tg sf qd
  have sp := spectrum_of tg jm cu sc
  have ht := height_of tg
  have wq := wallQuot_of qd
  have ch := chain_of tg jm cu sf qd sc ht wq
  have ca := colAnti_of tg jm ht
  have tf := transFin_of tg jm sf qd sp ch ca
  have tr := trans_of tf
  have ta := transAll_of tg tr
  have tk := tensorGK_of tg
  have wa := wallAlg_of tg jm qd sp
  have li := lieInv_holds
  have co := contract_of tg qd wa tk li wq
  have sz := semiZero_of qd wa li wq
  have sa := sphAll_of swStart_holds co sz
  exact kType_of tg ta tk sa young_holds

end PositivityTheory.Rg.Cz
