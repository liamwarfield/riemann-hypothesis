module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHW

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurInv
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurChain
noncomputable section

open MvPolynomial

namespace PI.FJMB

variable {R : Type*} [CommRing R] {σ : Type*}

private theorem sum_aeval_pderiv_X_mul_derivation {B : Type*} [CommRing B] [Algebra R B] (D : Derivation R B B)
    (φ : σ → B) (S : Finset σ) (hS : ∀ v, v ∉ S → D (φ v) = 0) (w : σ) :
    ∑ v ∈ S, aeval φ (pderiv v (X w : MvPolynomial σ R)) * D (φ v) = D (φ w) := by
  classical
  have key : ∀ v, aeval φ (pderiv v (X w : MvPolynomial σ R)) * D (φ v) =
      if w = v then D (φ v) else 0 := by
    intro v
    rw [pderiv_X]
    by_cases h : w = v
    · subst h
      simp
    · simp [Pi.single_apply, h]
  rw [Finset.sum_congr rfl (fun v _ => key v), Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (hS w h).symm

theorem deriv_aeval {B : Type*} [CommRing B] [Algebra R B] (D : Derivation R B B) (φ : σ → B)
    (S : Finset σ) (hS : ∀ v, v ∉ S → D (φ v) = 0) (f : MvPolynomial σ R) :
    D (aeval φ f) = ∑ v ∈ S, aeval φ (pderiv v f) * D (φ v) := by
  classical
  induction f using MvPolynomial.induction_on
  · rename_i a
    simp [aeval_C]
  · rename_i p q hp hq
    simp only [map_add (f := _), hp, hq, add_mul, Finset.sum_add_distrib]
  · rename_i p w hp
    have h1 : ∀ v, pderiv v (p * X w) = pderiv v p * X w + p * pderiv v (X w) := by
      intro v
      simp only [Derivation.leibniz, smul_eq_mul]
      ring
    simp only [h1, map_add (f := _), map_mul, aeval_X, add_mul, Finset.sum_add_distrib]
    have h2 : ∑ v ∈ S, aeval φ p * aeval φ (pderiv v (X w : MvPolynomial σ R)) * D (φ v) =
        aeval φ p * D (φ w) := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, sum_aeval_pderiv_X_mul_derivation D φ S hS w]
    have h3 : ∑ v ∈ S, aeval φ (pderiv v p) * φ w * D (φ v) =
        φ w * ∑ v ∈ S, aeval φ (pderiv v p) * D (φ v) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, h2, h3, ← hp]
    ring

theorem aeval_translate_eq {K : Type*} [Field K] [CharZero K] [Algebra R K] (f : MvPolynomial σ R)
    (S : Finset σ) (c : σ → MvPolynomial σ R) (hf : ∑ v ∈ S, c v * pderiv v f = 0) (y z : σ → K)
    (hz : ∀ v, v ∉ S → z v = 0)
    (hc : ∀ v ∈ S, aeval (fun w => Polynomial.C (y w) + Polynomial.X * Polynomial.C (z w)) (c v) =
      Polynomial.C (z v)) (t : K) :
    aeval (fun w => y w + t * z w) f = aeval y f := by
  classical
  set φ : σ → Polynomial K := fun w => Polynomial.C (y w) + Polynomial.X * Polynomial.C (z w)
    with hφ
  let D : Derivation R (Polynomial K) (Polynomial K) :=
    (Polynomial.derivative' : Derivation K (Polynomial K) (Polynomial K)).restrictScalars R
  have hD : ∀ q, D q = Polynomial.derivative q := fun q => rfl
  have hDφ : ∀ v, D (φ v) = Polynomial.C (z v) := by
    intro v
    rw [hD, hφ]
    simp
  have hS : ∀ v, v ∉ S → D (φ v) = 0 := by
    intro v hv
    rw [hDφ, hz v hv, map_zero]
  have hder : Polynomial.derivative (aeval φ f) = 0 := by
    rw [← hD, deriv_aeval D φ S hS f]
    calc ∑ v ∈ S, aeval φ (pderiv v f) * D (φ v) = ∑ v ∈ S, aeval φ (c v * pderiv v f) := by
          refine Finset.sum_congr rfl (fun v hv => ?_)
          rw [hDφ, map_mul, ← hc v hv, mul_comm]
      _ = aeval φ (∑ v ∈ S, c v * pderiv v f) := by rw [map_sum]
      _ = 0 := by rw [hf, map_zero]
  have hconst : aeval φ f = Polynomial.C ((aeval φ f).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_derivative_eq_zero hder)
  have heval : ∀ (s : K) (g : MvPolynomial σ R),
      (aeval φ g).eval s = aeval (fun w => y w + s * z w) g := by
    intro s g
    induction g using MvPolynomial.induction_on
    · rename_i a
      simp [aeval_C, Polynomial.algebraMap_apply]
    · rename_i p q hp hq
      simp only [map_add (f := _), Polynomial.eval_add, hp, hq]
    · rename_i p n hp
      rw [map_mul, aeval_X, Polynomial.eval_mul, hp, map_mul, aeval_X]
      congr 1
      simp only [hφ, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  have h0 : (aeval φ f).eval 0 = aeval y f := by
    have hy : (fun w => y w + 0 * z w) = y := by
      funext w
      simp
    rw [heval 0 f, hy]
  rw [← heval t f, ← h0, hconst, Polynomial.eval_C, Polynomial.eval_C]

end PI.FJMB
end
end

noncomputable section

open MvPolynomial

namespace PI.FJMB

variable {σ : Type*}

theorem bRow_apply {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) (P : MvPolynomial σ ℂ) :
    PI.FJM.bRow ι a b P = ∑ k : Fin n, X (ι (a, k)) * pderiv (ι (b, k)) P := by
  rw [PI.FJM.bRow, LinearMap.sum_apply]; simp

theorem bCol_apply {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) (P : MvPolynomial σ ℂ) :
    PI.FJM.bCol ι c d P = ∑ i : Fin m, X (ι (i, c)) * pderiv (ι (i, d)) P := by
  rw [PI.FJM.bCol, LinearMap.sum_apply]; simp

theorem translate_pairs {R : Type*} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq σ] (u w : κ → σ)
    (_hw : Function.Injective w) (huw : ∀ k k', u k ≠ w k') (f : MvPolynomial σ R)
    (h : ∑ k, X (u k) * pderiv (w k) f = 0) {K : Type*} [Field K] [CharZero K] [Algebra R K] (y : σ → K) (t : K) :
    aeval (fun v => y v + t * ∑ k, if w k = v then y (u k) else 0) f = aeval y f := by
  classical
  refine aeval_translate_eq f (Finset.univ.image w) (fun v => ∑ k, if w k = v then X (u k) else 0) ?_ y
    (fun v => ∑ k, if w k = v then y (u k) else 0) ?_ ?_ t
  · calc ∑ v ∈ Finset.univ.image w, (∑ k, if w k = v then (X (u k) : MvPolynomial σ R) else 0) * pderiv v f
        = ∑ k, ∑ v ∈ Finset.univ.image w, if w k = v then X (u k) * pderiv v f else 0 := by
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => ?_); split_ifs <;> simp
      _ = ∑ k, X (u k) * pderiv (w k) f := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.sum_ite_eq]; simp
      _ = 0 := h
  · intro v hv
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have : w k ≠ v := fun e => hv (by rw [← e]; exact Finset.mem_image_of_mem w (Finset.mem_univ k))
    simp [this]
  · intro v _
    have hz : ∀ k, (∑ k', if w k' = u k then (Polynomial.C (y (u k')) : Polynomial K) else 0) = 0 :=
      fun k => Finset.sum_eq_zero (fun k' _ => by simp [Ne.symm (huw k k')])
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, apply_ite (aeval _), aeval_X, map_zero, apply_ite Polynomial.C]
    simp only [hz, mul_zero, add_zero]

def fill {K : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) (M : Fin m → Fin n → K) (p : σ → K) : σ → K :=
  Function.extend ι (fun x => M x.1 x.2) p

theorem fill_ι {K : Type*} {m n : ℕ} {ι : Fin m × Fin n → σ} (hι : Function.Injective ι) (M : Fin m → Fin n → K)
    (p : σ → K) (x : Fin m × Fin n) : fill ι M p (ι x) = M x.1 x.2 :=
  hι.extend_apply _ _ _

theorem fill_not {K : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) (M : Fin m → Fin n → K)
    (p : σ → K) (v : σ) (hv : ∀ x, ι x ≠ v) : fill ι M p v = p v :=
  Function.extend_apply' _ _ _ (fun ⟨x, hx⟩ => hv x hx)

def rowAddM {K : Type*} [Field K] {m n : ℕ} (M : Fin m → Fin n → K) (a b : Fin m) (t : K) : Fin m → Fin n → K :=
  fun i k => if i = b then M i k + t * M a k else M i k

def colAddM {K : Type*} [Field K] {m n : ℕ} (M : Fin m → Fin n → K) (c d : Fin n) (t : K) : Fin m → Fin n → K :=
  fun i k => if k = d then M i k + t * M i c else M i k

theorem row_inv {m n : ℕ} (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (a b : Fin m) (hab : a ≠ b)
    (f : MvPolynomial σ ℂ) (hf : PI.FJM.bRow ι a b f = 0) {K : Type*} [Field K] [CharZero K] [Algebra ℂ K]
    (M : Fin m → Fin n → K) (p : σ → K) (t : K) :
    aeval (fill ι (rowAddM M a b t) p) f = aeval (fill ι M p) f := by
  classical
  have key := translate_pairs (R := ℂ) (fun k : Fin n => ι (a, k)) (fun k => ι (b, k))
    (fun k k' e => by have := hι e; simp at this; exact this)
    (fun k k' e => hab (by have := hι e; simp at this; exact this.1)) f (by rw [← bRow_apply]; exact hf)
    (fill ι M p) t
  refine Eq.trans ?_ key
  congr 1
  congr 1
  funext v
  by_cases hv : ∃ x, ι x = v
  · obtain ⟨⟨i, k⟩, rfl⟩ := hv
    rw [fill_ι hι, fill_ι hι]
    simp only [rowAddM]
    have hs : (∑ k', if ι (b, k') = ι (i, k) then fill ι M p (ι (a, k')) else 0) = if i = b then M a k else 0 := by
      simp only [hι.eq_iff, Prod.mk.injEq, fill_ι hι]
      by_cases hib : i = b
      · subst hib; simp
      · simp [Ne.symm hib, hib]
    rw [hs]; split_ifs <;> simp
  · push Not at hv
    rw [fill_not _ _ _ _ hv, fill_not _ _ _ _ hv]
    have : (∑ k', if ι (b, k') = v then fill ι M p (ι (a, k')) else 0) = 0 :=
      Finset.sum_eq_zero (fun k' _ => by simp [hv (b, k')])
    rw [this, mul_zero, add_zero]

theorem col_inv {m n : ℕ} (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (c d : Fin n) (hcd : c ≠ d)
    (f : MvPolynomial σ ℂ) (hf : PI.FJM.bCol ι c d f = 0) {K : Type*} [Field K] [CharZero K] [Algebra ℂ K]
    (M : Fin m → Fin n → K) (p : σ → K) (t : K) :
    aeval (fill ι (colAddM M c d t) p) f = aeval (fill ι M p) f := by
  classical
  have key := translate_pairs (R := ℂ) (fun i : Fin m => ι (i, c)) (fun i => ι (i, d))
    (fun i i' e => by have := hι e; simp at this; exact this)
    (fun i i' e => hcd (by have := hι e; simp at this; exact this.2)) f (by rw [← bCol_apply]; exact hf)
    (fill ι M p) t
  refine Eq.trans ?_ key
  congr 1
  congr 1
  funext v
  by_cases hv : ∃ x, ι x = v
  · obtain ⟨⟨i, k⟩, rfl⟩ := hv
    rw [fill_ι hι, fill_ι hι]
    simp only [colAddM]
    have hs : (∑ i', if ι (i', d) = ι (i, k) then fill ι M p (ι (i', c)) else 0) = if k = d then M i c else 0 := by
      simp only [hι.eq_iff, Prod.mk.injEq, fill_ι hι]
      by_cases hkd : k = d
      · subst hkd; simp
      · simp [Ne.symm hkd, hkd]
    rw [hs]; split_ifs <;> simp
  · push Not at hv
    rw [fill_not _ _ _ _ hv, fill_not _ _ _ _ hv]
    have : (∑ i', if ι (i', d) = v then fill ι M p (ι (i', c)) else 0) = 0 :=
      Finset.sum_eq_zero (fun i' _ => by simp [hv (i', d)])
    rw [this, mul_zero, add_zero]

end PI.FJMB
end
end

noncomputable section

open MvPolynomial Classical

namespace PI.FJMB

variable {σ : Type*}

def HWB {m n : ℕ} (ι : Fin m × Fin n → σ) (f : MvPolynomial σ ℂ) : Prop :=
  (∀ a b : Fin m, a < b → PI.FJM.bRow ι a b f = 0) ∧ (∀ c d : Fin n, c < d → PI.FJM.bCol ι c d f = 0)

def offD {m n : ℕ} (ι : Fin m × Fin n → σ) : Set σ := {v | ∃ i k, ι (i, k) = v ∧ (i : ℕ) ≠ k}

def killS (S : Set σ) : σ → MvPolynomial σ ℂ := fun v => if v ∈ S then 0 else X v

def edge {m n : ℕ} (ι : Fin (m + 1) × Fin (n + 1) → σ) : Set σ :=
  {v | (∃ l : Fin n, ι (0, l.succ) = v) ∨ (∃ j : Fin m, ι (j.succ, 0) = v)}

theorem aeval_aeval' {K : Type*} [CommRing K] [Algebra ℂ K] (g : σ → K) (φ : σ → MvPolynomial σ ℂ)
    (f : MvPolynomial σ ℂ) : aeval g (aeval φ f) = aeval (fun v => aeval g (φ v)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f h hf hh => simp only [map_add (f := _), hf, hh]
  | mul_X f w hf => simp only [map_mul, aeval_X, hf]

theorem aeval_killS_empty (f : MvPolynomial σ ℂ) : aeval (killS (∅ : Set σ)) f = f := by
  have : killS (∅ : Set σ) = X := by funext v; simp [killS]
  rw [this, aeval_X_left_apply]

theorem aeval_killS_union (S T : Set σ) (f : MvPolynomial σ ℂ) :
    aeval (killS S) (aeval (killS T) f) = aeval (killS (S ∪ T)) f := by
  rw [aeval_aeval']
  congr 2
  funext v
  by_cases hT : v ∈ T
  · simp [killS, hT]
  · by_cases hS : v ∈ S <;> simp [killS, hT, hS]

theorem pderiv_aeval_killS (S : Set σ) (w : σ) (hw : w ∉ S) (f : MvPolynomial σ ℂ) :
    pderiv w (aeval (killS S) f) = aeval (killS S) (pderiv w f) := by
  have h := deriv_aeval (R := ℂ) (pderiv w) (killS S) {w} (fun v hv => by
    have hv' : v ≠ w := by simpa using hv
    by_cases h : v ∈ S <;> simp [killS, h, pderiv_X_of_ne hv']) f
  rw [h]
  simp [killS, hw]

theorem aeval_killS_of_zero {K : Type*} [CommRing K] [Algebra ℂ K] (S : Set σ) (y : σ → K)
    (hy : ∀ v ∈ S, y v = 0) (f : MvPolynomial σ ℂ) : aeval y (aeval (killS S) f) = aeval y f := by
  rw [aeval_aeval']
  congr 2
  funext v
  by_cases h : v ∈ S
  · simp [killS, h, hy v h]
  · simp [killS, h]

section Step

variable {m n : ℕ} (ι : Fin (m + 1) × Fin (n + 1) → σ) (hι : Function.Injective ι)
include hι

theorem edge_succ_succ (i : Fin m) (k : Fin n) : ι (i.succ, k.succ) ∉ edge ι := by
  rintro (⟨l, hl⟩ | ⟨j, hj⟩)
  · have := hι hl; simp at this; exact Fin.succ_ne_zero _ this.1.symm
  · have := hι hj; simp at this; exact Fin.succ_ne_zero _ this.2.symm

theorem hwb_restrict (f : MvPolynomial σ ℂ) (hf : HWB ι f) :
    HWB (fun x : Fin m × Fin n => ι (x.1.succ, x.2.succ)) (aeval (killS (edge ι)) f) := by
  constructor
  · intro a b hab
    rw [bRow_apply]
    have h0 := congrArg (aeval (killS (edge ι))) (hf.1 a.succ b.succ (Fin.succ_lt_succ_iff.2 hab))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [bRow_apply, map_zero, map_sum, Fin.sum_univ_succ] at h0
    have e0 : ι (a.succ, 0) ∈ edge ι := Or.inr ⟨a, rfl⟩
    simp only [map_mul, aeval_X, killS, e0, if_true, zero_mul, zero_add] at h0
    rw [← h0]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [pderiv_aeval_killS _ _ (edge_succ_succ ι hι b k)]
    simp [edge_succ_succ ι hι a k]
  · intro c d hcd
    rw [bCol_apply]
    have h0 := congrArg (aeval (killS (edge ι))) (hf.2 c.succ d.succ (Fin.succ_lt_succ_iff.2 hcd))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [bCol_apply, map_zero, map_sum, Fin.sum_univ_succ] at h0
    have e0 : ι (0, c.succ) ∈ edge ι := Or.inl ⟨c, rfl⟩
    simp only [map_mul, aeval_X, killS, e0, if_true, zero_mul, zero_add] at h0
    rw [← h0]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pderiv_aeval_killS _ _ (edge_succ_succ ι hι i d)]
    simp [edge_succ_succ ι hι i c]

theorem offD_step : offD (fun x : Fin m × Fin n => ι (x.1.succ, x.2.succ)) ∪ edge ι = offD ι := by
  ext v
  constructor
  · rintro (⟨i, k, rfl, hik⟩ | (⟨l, rfl⟩ | ⟨j, rfl⟩))
    · exact ⟨i.succ, k.succ, rfl, by simpa using hik⟩
    · exact ⟨0, l.succ, rfl, by simp⟩
    · exact ⟨j.succ, 0, rfl, by simp⟩
  · rintro ⟨i, k, rfl, hik⟩
    cases i using Fin.cases with
    | zero =>
      cases k using Fin.cases with
      | zero => simp at hik
      | succ l => exact Or.inr (Or.inl ⟨l, rfl⟩)
    | succ i =>
      cases k using Fin.cases with
      | zero => exact Or.inr (Or.inr ⟨i, rfl⟩)
      | succ l => exact Or.inl ⟨i, l, rfl, by simpa using hik⟩

end Step

end PI.FJMB
