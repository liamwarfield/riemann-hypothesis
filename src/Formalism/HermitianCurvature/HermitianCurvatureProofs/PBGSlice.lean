module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWave
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGDegW
open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section eqgv

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {S : Type}

theorem eqGV_refl (x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) : EqGV x x := fun _ _ _ => rfl

theorem eqGV_trans {x y z : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (h₁ : EqGV x y) (h₂ : EqGV y z) : EqGV x z :=
  fun a g hg => (h₁ a g hg).trans (h₂ a g hg)

theorem eqGV_add_smul {x x' y y' : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (c : ℂ) (h₁ : EqGV x x') (h₂ : EqGV y y') :
    EqGV (x + c • y) (x' + c • y') := fun a g hg => by
  simp only [Pi.add_apply, Pi.smul_apply]; rw [h₁ a g hg, h₂ a g hg]

end eqgv

section deg

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def SlicePoly {k r : ℕ} (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ r)
    (h : C.LPt) (hh : D.ptSize h = j) : Prop :=
  ∀ (w' : List C.Letter) (b : Bool) (δ : ℝ) (e : Fin 2), ∃ Cf : Fin (j + 1) → Wd.Ix (Fin w'.length) →
      B.Mat k (r - j) → (Wq →L[ℂ] Wp),
    Cf (Fin.last j) = (if e = 0 then KB.slv T F j hj w' h hh else 0) ∧
    (∀ l, ∃ ε, ∀ a, JC.NiceCoef (T.bs j) ε (Cf l a)) ∧
    ∀ t : ℝ, EqGV (fun a => KB.slv T F j hj ((b, t + δ) :: w') h hh (Fin.cons e a)) (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • Cf l)

variable {P : M.Par} (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r)
  (w : List C.Letter) (h h' : C.LPt) (hh : D.ptSize h = j) (hh' : D.ptSize h' = j) (s : ℂ)
  (Mo : (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) →ₗ[ℂ]
      (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)))

def xP (ys : List ℝ) : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp) :=
  KB.waveG (p.T.bs j) s (KB.plusW ys w) (KB.onOld (⇑Mo) ys (KB.slv p.T F j hj (KB.plusW ys w) h hh))

def xM (ys : List ℝ) : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp) :=
  KB.slv p.T F j hj (KB.minusW ys w) h' hh'

def Wv (ys : List ℝ) : ℂ := KB.pairJ (p.form j hj w) ys (xP p F j hj w h hh s Mo ys) (xM p F j hj w h' hh' ys)

theorem form_eq : p.form j hj w = D.formLev p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w := rfl

theorem xP_cons0 (t : ℝ) (ys : List ℝ) :
    (fun e' => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 0 e')) =
      KB.waveG (p.T.bs j) s (KB.plusW ys w) (KB.onOld (⇑Mo) ys
        (fun a => KB.slv p.T F j hj ((true, t) :: KB.plusW ys w) h hh (Fin.cons 0 a))) := by
  funext e'
  exact waveG_cons0 (p.T.bs j) s t (KB.plusW ys w) _ e'

theorem xP_cons1 (t : ℝ) (ys : List ℝ) :
    (fun e' => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 1 e')) =
      KB.waveG (p.T.bs j) s (KB.plusW ys w) (KB.onOld (⇑Mo) ys
        (fun a => KB.slv p.T F j hj ((true, t) :: KB.plusW ys w) h hh (Fin.cons 1 a))) +
      s • KB.waveG (p.T.bs j) s (KB.plusW ys w) (KB.onOld (⇑Mo) ys
        (fun a => KB.slv p.T F j hj ((true, t) :: KB.plusW ys w) h hh (Fin.cons 0 a))) := by
  funext e'
  exact waveG_cons1 (p.T.bs j) s t (KB.plusW ys w) _ e'

theorem conj_tpow (t : ℝ) (m : ℕ) : conj ((t : ℂ) ^ m) = (t : ℂ) ^ m := by
  rw [map_pow, Complex.conj_ofReal]

theorem wv_step (hSP : SlicePoly p.T F j hj h hh) (hSP' : SlicePoly p.T F j hj h' hh')
    (hMo : ∀ ε x, (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → ∀ e, JC.NiceCoef (p.T.bs j) ε (Mo x e)) (ys : List ℝ) :
    ∃ c : Fin (2 * j + 1) → ℂ, c (Fin.last (2 * j)) = s * Wv p F j hj w h h' hh hh' s Mo ys ∧
      ∀ t : ℝ, Wv p F j hj w h h' hh hh' s Mo (t :: ys) = ∑ q : Fin (2 * j + 1), ((t : ℂ) ^ (q : ℕ)) * c q := by
  obtain ⟨C0, hC0l, hC0n, hC0⟩ := hSP (KB.plusW ys w) true 0 0
  obtain ⟨C1, hC1l, hC1n, hC1⟩ := hSP (KB.plusW ys w) true 0 1
  obtain ⟨D0, hD0l, hD0n, hD0⟩ := hSP' (KB.minusW ys w) false 1 0
  obtain ⟨D1, hD1l, hD1n, hD1⟩ := hSP' (KB.minusW ys w) false 1 1
  set Bs := p.T.bs j with hBs
  set A0 : Fin (j + 1) → Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp) :=
    fun l => KB.waveG Bs s (KB.plusW ys w) (KB.onOld (⇑Mo) ys (C0 l)) with hA0
  set A1 : Fin (j + 1) → Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp) :=
    fun l => KB.waveG Bs s (KB.plusW ys w) (KB.onOld (⇑Mo) ys (C1 l)) + s • KB.waveG Bs s (KB.plusW ys w) (KB.onOld (⇑Mo) ys (C0 l)) with hA1
  have hMoc : ∀ x y, EqGV x y → EqGV (Mo x) (Mo y) := mo_congrGV Bs Mo hMo
  have nA : ∀ (Cf : Fin (j + 1) → Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)),
      (∀ l, ∃ ε, ∀ a, JC.NiceCoef Bs ε (Cf l a)) → ∀ l, DecV (KB.waveG Bs s (KB.plusW ys w) (KB.onOld (⇑Mo) ys (Cf l))) := by
    intro Cf hn l
    obtain ⟨ε, hε⟩ := hn l
    exact decV_of_nice (Formalism.FourierDecayAlt.P.PBFV.waveG_nice Bs ε s (KB.plusW ys w) _
      (onOld_nice Bs ε (⇑Mo) (fun x hx => hMo ε x hx) ys (Cf l) hε))
  have dA0 : ∀ l, DecV (A0 l) := nA C0 hC0n
  have dA1 : ∀ l, DecV (A1 l) := fun l => decV_add (nA C1 hC1n l) (decV_smul s (nA C0 hC0n l))
  have dD0 : ∀ l, DecV (D0 l) := fun l => by obtain ⟨ε, hε⟩ := hD0n l; exact decV_of_nice hε
  have dD1 : ∀ l, DecV (D1 l) := fun l => by obtain ⟨ε, hε⟩ := hD1n l; exact decV_of_nice hε

  have ePlus : ∀ (t : ℝ) (Cf : Fin (j + 1) → Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (e : Fin 2),
      EqGV (fun a => KB.slv p.T F j hj ((true, t + 0) :: KB.plusW ys w) h hh (Fin.cons e a)) (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • Cf l) →
      EqGV (KB.waveG Bs s (KB.plusW ys w) (KB.onOld (⇑Mo) ys (fun a => KB.slv p.T F j hj ((true, t) :: KB.plusW ys w) h hh (Fin.cons e a))))
        (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • KB.waveG Bs s (KB.plusW ys w) (KB.onOld (⇑Mo) ys (Cf l))) := by
    intro t Cf e hE
    rw [add_zero] at hE
    have h1 := waveG_congrGV Bs s (KB.plusW ys w) _ _ (onOld_congrGV (⇑Mo) hMoc ys _ _ hE)
    rw [onOld_sum, waveG_sum] at h1
    exact h1
  have e0 : ∀ t : ℝ, EqGV (fun e' => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 0 e'))
      (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • A0 l) := by
    intro t
    rw [xP_cons0]
    exact ePlus t C0 0 (hC0 t)
  have e1 : ∀ t : ℝ, EqGV (fun e' => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 1 e'))
      (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • A1 l) := by
    intro t
    rw [xP_cons1]
    have := eqGV_add_smul s (ePlus t C1 1 (hC1 t)) (ePlus t C0 0 (hC0 t))
    refine eqGV_trans this (fun a g hg => ?_)
    simp only [hA1, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_add, Finset.smul_sum, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [smul_comm]

  have hX : ∀ t : ℝ, Wv p F j hj w h h' hh hh' s Mo (t :: ys) =
      ∑ l : Fin (j + 1), ∑ m : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) * ((t : ℂ) ^ (m : ℕ)) *
        (KB.pairJ (p.form j hj w) ys (A1 l) (D0 m) - KB.pairJ (p.form j hj w) ys (A0 l) (D1 m)) := by
    intro t
    show KB.pairJ (p.form j hj w) ys (fun e => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 1 e))
        (fun e => xM p F j hj w h' hh' (t :: ys) (Fin.cons 0 e)) -
      KB.pairJ (p.form j hj w) ys (fun e => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 0 e))
        (fun e => xM p F j hj w h' hh' (t :: ys) (Fin.cons 1 e)) = _
    rw [form_eq]
    have c1 := pairJ_formLev_congrGV p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys
      (fun e => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 1 e)) (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • A1 l)
      (fun e => xM p F j hj w h' hh' (t :: ys) (Fin.cons 0 e)) (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • D0 l)
      (e1 t) (hD0 t)
    have c2 := pairJ_formLev_congrGV p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys
      (fun e => xP p F j hj w h hh s Mo (t :: ys) (Fin.cons 0 e)) (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • A0 l)
      (fun e => xM p F j hj w h' hh' (t :: ys) (Fin.cons 1 e)) (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • D1 l)
      (e0 t) (hD1 t)
    rw [c1, c2]
    rw [pairJ_sum_sum P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ A1 D0 dA1 dD0,
      pairJ_sum_sum P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys _ _ _ _ A0 D1 dA0 dD1, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [conj_tpow]
    ring
  set X : Fin (j + 1) → Fin (j + 1) → ℂ := fun l m =>
    KB.pairJ (p.form j hj w) ys (A1 l) (D0 m) - KB.pairJ (p.form j hj w) ys (A0 l) (D1 m) with hXdef
  refine ⟨fun q => ∑ l : Fin (j + 1), ∑ m : Fin (j + 1), if l.val + m.val = q.val then X l m else 0, ?_, fun t => ?_⟩
  ·
    dsimp only
    rw [Finset.sum_eq_single (Fin.last j)]
    · rw [Finset.sum_eq_single (Fin.last j)]
      · rw [if_pos (by simp; omega)]
        have z0 : ∀ (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), DecV y →
            KB.pairJ (p.form j hj w) ys 0 y = 0 := by
          intro y hy
          have := pairJ_sesq_left P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys 0 0 y 1 decV_zero decV_zero hy
          rw [one_smul, add_zero, one_mul, ← form_eq p j hj w] at this
          linear_combination -this
        have z1 : ∀ (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), DecV x →
            KB.pairJ (p.form j hj w) ys x 0 = 0 := by
          intro x hx
          have := pairJ_sesq_right P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys x 0 0 1 hx decV_zero decV_zero
          rw [one_smul, add_zero, map_one, one_mul, ← form_eq p j hj w] at this
          linear_combination -this
        have hA1l : A1 (Fin.last j) = 0 + s • xP p F j hj w h hh s Mo ys := by
          simp only [hA1, hC1l, hC0l, if_pos, show ((1 : Fin 2) = 0) = False from by decide, if_false,
            onOld_zero, waveG_zero]
          rfl
        have hD0l' : D0 (Fin.last j) = xM p F j hj w h' hh' ys := by rw [hD0l, if_pos rfl]; rfl
        have hD1l' : D1 (Fin.last j) = 0 := by rw [hD1l]; simp
        have dxP : DecV (xP p F j hj w h hh s Mo ys) := by
          have h1 := dA1 (Fin.last j)
          rw [hA1l, zero_add] at h1
          have h2 := nA C0 hC0n (Fin.last j)
          simp only [hC0l, if_pos] at h2
          exact h2
        have dxM : DecV (xM p F j hj w h' hh' ys) := by rw [← hD0l']; exact dD0 _
        simp only [hXdef]
        rw [hA1l, hD0l', hD1l', z1 _ (dA0 _)]
        have := pairJ_sesq_left P p.T (M.sgn P p.l0) ⟨j, Nat.lt_succ_of_le hj⟩ w ys 0 (xP p F j hj w h hh s Mo ys)
          (xM p F j hj w h' hh' ys) s decV_zero dxP dxM
        rw [← form_eq p j hj w] at this
        rw [this, z0 _ dxM]
        simp only [Wv]
        ring
      · intro m _ hm
        rw [if_neg]
        have := m.isLt
        have hm' : m.val ≠ j := fun e => hm (Fin.ext (by simp [e]))
        simp; omega
      · simp
    · intro l _ hl
      apply Finset.sum_eq_zero
      intro m _
      rw [if_neg]
      have := l.isLt
      have := m.isLt
      have hl' : l.val ≠ j := fun e => hl (Fin.ext (by simp [e]))
      simp; omega
    · simp
  ·
    have key : ∀ l m : Fin (j + 1), ∑ q : Fin (2 * j + 1), ((t : ℂ) ^ (q : ℕ)) * (if l.val + m.val = q.val then X l m else 0) =
        ((t : ℂ) ^ (l : ℕ)) * ((t : ℂ) ^ (m : ℕ)) * X l m := by
      intro l m
      rw [Finset.sum_eq_single ⟨l.val + m.val, by omega⟩]
      · rw [if_pos rfl, pow_add]
      · intro q _ hq
        rw [if_neg, mul_zero]
        intro e
        exact hq (Fin.ext e.symm)
      · simp
    rw [hX t]
    calc ∑ l : Fin (j + 1), ∑ m : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) * ((t : ℂ) ^ (m : ℕ)) * X l m
        = ∑ l : Fin (j + 1), ∑ m : Fin (j + 1), ∑ q : Fin (2 * j + 1),
            ((t : ℂ) ^ (q : ℕ)) * (if l.val + m.val = q.val then X l m else 0) := by
          simp only [key]
      _ = ∑ q : Fin (2 * j + 1), ∑ l : Fin (j + 1), ∑ m : Fin (j + 1),
            ((t : ℂ) ^ (q : ℕ)) * (if l.val + m.val = q.val then X l m else 0) := by
          refine (Finset.sum_congr rfl (fun l _ => Finset.sum_comm)).trans ?_
          exact Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro q _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.mul_sum]

end deg

def Lst (K m : ℕ) (y : Fin K → ℝ) : List ℝ := List.ofFn fun b : Fin m => if hb : m - 1 - b < K then y ⟨m - 1 - b, hb⟩ else 0

theorem lst_succ (K : ℕ) (a : Fin K) (y : Fin K → ℝ) (t : ℝ) :
    Lst K ((a : ℕ) + 1) (Function.update y a t) = t :: Lst K a y := by
  unfold Lst
  rw [List.ofFn_succ]
  congr 1
  · rw [dite_eq_left (by omega)]
    have e : (⟨(a : ℕ) + 1 - 1 - ((0 : Fin ((a : ℕ) + 1)) : ℕ), by omega⟩ : Fin K) = a := Fin.ext (by simp)
    rw [e, Function.update_self]
  · congr 1
    funext i
    have hi := i.isLt
    rw [dite_eq_left (by simp; omega), dite_eq_left (by omega)]
    have e : (⟨(a : ℕ) + 1 - 1 - (i.succ : ℕ), by simp; omega⟩ : Fin K) = ⟨(a : ℕ) - 1 - i, by omega⟩ :=
      Fin.ext (by simp; omega)
    rw [e, Function.update_of_ne]
    intro h'
    have := congrArg Fin.val h'
    simp at this
    omega

theorem lst_full (K : ℕ) (z : Fin K → ℝ) : Lst K K z = List.ofFn fun b => z (Fin.rev b) := by
  unfold Lst
  congr 1
  funext b
  rw [dite_eq_left (by omega)]
  congr 1
  ext
  simp [Fin.val_rev]
  omega

section final

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def SlicePolyAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F → ∀ (j : ℕ) (hj : j ≤ P.r) (h : C.LPt)
    (hh : D.IsLocPt h j), SlicePoly p.T F j hj h hh.2

theorem degWave_of (hS : SlicePolyAll) : KB.DegWave := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h h' hh hh' K grid s Mo hMo hF hgrid
  set W : ℕ → (Fin K → ℝ) → ℂ := fun m y => Wv p F j hj w h h' hh.2 hh'.2 s Mo (Lst K m y) with hW
  have hPS : F7.PolyStep K (2 * j) (fun _ => s) W := by
    intro a y
    obtain ⟨c, hc, hcs⟩ := wv_step p F j hj w h h' hh.2 hh'.2 s Mo (hS Wp Wq P p F hF j hj h hh)
      (hS Wp Wq P p F hF j hj h' hh') hMo (Lst K a y)
    refine ⟨c, ?_, fun t => ?_⟩
    · rw [hc, smul_eq_mul]
    · simp only [hW]
      rw [lst_succ, hcs t]
      simp only [smul_eq_mul]
  have hinj : ∀ a, Function.Injective (fun i => grid (Fin.rev a) i) := fun a => hgrid _
  have hE := Formalism.FourierDecayAlt.P.extract_K_bound ℂ K (2 * j) (fun _ => s) W (fun a => grid (Fin.rev a)) hPS hinj (fun _ => 0)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hE
  have hW0 : W 0 (fun _ => 0) = p.form j hj w (KB.waveG (p.T.bs j) s w (Mo (KB.slv p.T F j hj w h hh.2)))
      (KB.slv p.T F j hj w h' hh'.2) := rfl
  rw [hW0] at hE
  rw [hE]

  refine Fintype.sum_equiv ((Fin.revPerm).arrowCongr (Equiv.refl _)) _ _ (fun n => ?_)
  simp only [hW, smul_eq_mul]
  rw [lst_full]
  have e1 : (fun b : Fin K => grid (Fin.rev (Fin.rev b)) (n (Fin.rev b))) =
      fun b => grid b ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (2 * j + 1)))) n b) := by
    funext b
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  have e2 : (∏ a : Fin K, F7.lagCo (grid (Fin.rev a)) (n a)) =
      ∏ a : Fin K, F7.lagCo (grid a) ((Fin.revPerm.arrowCongr (Equiv.refl (Fin (2 * j + 1)))) n a) := by
    refine Fintype.prod_equiv Fin.revPerm _ _ (fun a => ?_)
    simp [Equiv.arrowCongr_apply, Fin.revPerm]
  rw [e1, e2]
  rfl

end final

end Formalism.FourierDecayAlt.P.PBG
end
end

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section cpt

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem cpt_zero (Bs : B.RealPlaceData k ρ Wp Wq) : KB.CptCoef Bs (fun _ => (0 : Wq →L[ℂ] Wp)) :=
  ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero, ⟨0, fun _ _ h => (h rfl).elim⟩, ⟨1, one_pos, fun _ _ h => (h rfl).elim⟩⟩

theorem cpt_add_smul (Bs : B.RealPlaceData k ρ Wp Wq) {F₁ F₂ : B.Mat k ρ → (Wq →L[ℂ] Wp)} (c : ℂ)
    (h₁ : KB.CptCoef Bs F₁) (h₂ : KB.CptCoef Bs F₂) : KB.CptCoef Bs (F₁ + c • F₂) := by
  obtain ⟨s₁, ⟨R₁, hR₁⟩, ⟨ε₁, hε₁, hG₁⟩⟩ := h₁
  obtain ⟨s₂, ⟨R₂, hR₂⟩, ⟨ε₂, hε₂, hG₂⟩⟩ := h₂
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add s₁ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul c s₂), ⟨max R₁ R₂, fun g hg hne => ?_⟩,
    ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun g hg hne => ?_⟩⟩
  · by_cases h0 : F₁ g = 0
    · have : F₂ g ≠ 0 := fun h2 => hne (by simp [h0, h2])
      exact (hR₂ g hg this).trans (le_max_right _ _)
    · exact (hR₁ g hg h0).trans (le_max_left _ _)
  · by_cases h0 : F₁ g = 0
    · have : F₂ g ≠ 0 := fun h2 => hne (by simp [h0, h2])
      exact (min_le_right _ _).trans (hG₂ g hg this)
    · exact (min_le_left _ _).trans (hG₁ g hg h0)

theorem cpt_sum (Bs : B.RealPlaceData k ρ Wp Wq) {ι : Type} (S : Finset ι) (c : ι → ℂ) (F : ι → B.Mat k ρ → (Wq →L[ℂ] Wp))
    (hF : ∀ i, KB.CptCoef Bs (F i)) : KB.CptCoef Bs (∑ i ∈ S, c i • F i) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact cpt_zero Bs
  | insert b t hb ih =>
    rw [Finset.sum_insert hb, add_comm]
    exact cpt_add_smul Bs (c b) ih (hF b)

theorem nice_of_cpt (Bs : B.RealPlaceData k ρ Wp Wq) {F : B.Mat k ρ → (Wq →L[ℂ] Wp)} (h : KB.CptCoef Bs F) :
    ∃ ε, JC.NiceCoef Bs ε F := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, -, hG⟩⟩ := h
  refine ⟨ε, hs, fun A m => Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k ρ R)
    (fun g hg hgC => ?_) A m, hG⟩
  by_contra h0
  exact hgC (hR g hg h0)

theorem nice_vec_of_cpt {S : Type} [Fintype S] (Bs : B.RealPlaceData k ρ Wp Wq) {x : S → B.Mat k ρ → (Wq →L[ℂ] Wp)}
    (h : ∀ a, KB.CptCoef Bs (x a)) : ∃ ε, ∀ a, JC.NiceCoef Bs ε (x a) := by
  classical
  have hx : ∀ a, KB.CptCoef Bs (x a) := h

  choose εf hεf using fun a => (hx a).2.2
  by_cases hS : Nonempty S
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty εf, fun a => ?_⟩
    obtain ⟨ε', hε'⟩ := nice_of_cpt Bs (hx a)
    refine ⟨hε'.1, hε'.2.1, fun g hg hne => ?_⟩
    exact (Finset.inf'_le _ (Finset.mem_univ a)).trans ((hεf a).2 g hg hne)
  · refine ⟨0, fun a => (hS ⟨a⟩).elim⟩

end cpt

section shift

theorem poly_shift {E : Type} [AddCommGroup E] [Module ℂ E] (d : ℕ) (c : Fin (d + 1) → E) (δ : ℂ) :
    ∃ c' : Fin (d + 1) → E, c' (Fin.last d) = c (Fin.last d) ∧
      ∀ t : ℂ, ∑ l : Fin (d + 1), (t + δ) ^ (l : ℕ) • c l = ∑ m : Fin (d + 1), t ^ (m : ℕ) • c' m := by
  refine ⟨fun m => ∑ l : Fin (d + 1),
    (if (m : ℕ) ≤ l then (((l : ℕ).choose m : ℂ) * δ ^ ((l : ℕ) - m)) else 0) • c l, ?_, fun t => ?_⟩
  · dsimp only
    rw [Finset.sum_eq_single (Fin.last d)]
    · simp
    · intro l _ hl
      have := l.isLt
      have hl' : (l : ℕ) ≠ d := fun e => hl (Fin.ext (by simp [e]))
      rw [if_neg (by simp; omega), zero_smul]
    · simp
  · simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [← Finset.sum_smul]
    congr 1
    have hl := l.isLt
    rw [Fin.sum_univ_eq_sum_range (fun m => t ^ m * if m ≤ (l : ℕ) then ((l : ℕ).choose m : ℂ) * δ ^ ((l : ℕ) - m) else 0)
      (d + 1)]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (d + 1)) (fun m => m ≤ (l : ℕ))]
    have h1 : (Finset.range (d + 1)).filter (fun m => m ≤ (l : ℕ)) = Finset.range ((l : ℕ) + 1) := by
      ext m; simp; omega
    rw [h1, Finset.sum_eq_zero (s := (Finset.range (d + 1)).filter (fun m => ¬ m ≤ (l : ℕ)))
      (fun m hm => by simp at hm; rw [if_neg (by omega), mul_zero]), add_zero, add_pow]
    apply Finset.sum_congr rfl
    intro m hm
    simp at hm
    rw [if_pos (by omega)]
    ring

end shift

section vand

theorem vand_ident {n : ℕ} (τ : Fin n → ℂ) (hτ : Function.Injective τ) (t : ℂ) (m : Fin n) :
    ∑ i : Fin n, (∑ l : Fin n, t ^ (l : ℕ) * (Matrix.vandermonde τ)⁻¹ l i) * τ i ^ (m : ℕ) = t ^ (m : ℕ) := by
  have hdet : (Matrix.vandermonde τ).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hτ
  have hinv : (Matrix.vandermonde τ)⁻¹ * Matrix.vandermonde τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  calc ∑ i : Fin n, (∑ l : Fin n, t ^ (l : ℕ) * (Matrix.vandermonde τ)⁻¹ l i) * τ i ^ (m : ℕ)
      = ∑ l : Fin n, t ^ (l : ℕ) * ∑ i : Fin n, (Matrix.vandermonde τ)⁻¹ l i * Matrix.vandermonde τ i m := by
        simp only [Finset.sum_mul, Finset.mul_sum, Matrix.vandermonde_apply]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro l _; apply Finset.sum_congr rfl; intro i _; ring
    _ = ∑ l : Fin n, t ^ (l : ℕ) * (1 : Matrix (Fin n) (Fin n) ℂ) l m := by
        apply Finset.sum_congr rfl; intro l _; rw [← Matrix.mul_apply, hinv]
    _ = t ^ (m : ℕ) := by
        simp [Matrix.one_apply]

theorem vand_row {n : ℕ} (τ : Fin n → ℂ) (hτ : Function.Injective τ) (l m : Fin n) :
    ∑ i : Fin n, (Matrix.vandermonde τ)⁻¹ l i * τ i ^ (m : ℕ) = if l = m then 1 else 0 := by
  have hdet : (Matrix.vandermonde τ).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hτ
  have hinv : (Matrix.vandermonde τ)⁻¹ * Matrix.vandermonde τ = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)
  have := congrFun (congrFun hinv l) m
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simpa [Matrix.vandermonde_apply] using this

end vand

section slicepoly

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem sliceAt_zero (z z' : Fin (2 * r + k + 1) → ℂ) (p : C.LPt) :
    D.sliceAt k r z z' (fun _ => (0 : Wq →L[ℂ] Wp)) p = fun _ => 0 := by
  funext γ
  unfold D.sliceAt
  split_ifs
  · simp [U.PhiFun, D.castF]
  · rfl

theorem slicePoly_of_pt (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef T.base F)
    (j : ℕ) (hj : j ≤ r) (hj1 : 1 ≤ j) (h : C.LPt) (hh : D.IsLocPt h j) (w' : List C.Letter) (b : Bool) (δ : ℝ)
    (e : Fin 2)
    (hpt : ∀ (a : Wd.Ix (Fin w'.length)), ∀ g ∈ B.GV k r, Dmin k r T.base.z T.base.z' g ⟨j, by omega⟩ ≠ 0 →
      ∃ c : Fin (j + 1) → (Wq →L[ℂ] Wp), c (Fin.last j) = (if e = 0 then D.uwG k r T.base.z T.base.z' F j hj w' a g else 0) ∧
        ∀ t : ℝ, D.uwG k r T.base.z T.base.z' F j hj ((b, t + δ) :: w') (Fin.cons e a) g = ∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • c l) :
    ∃ Cf : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp),
      Cf (Fin.last j) = (if e = 0 then KB.slv T F j hj w' h hh.2 else 0) ∧
      (∀ l, ∃ ε, ∀ a, JC.NiceCoef (T.bs j) ε (Cf l a)) ∧
      ∀ t : ℝ, EqGV (fun a => KB.slv T F j hj ((b, t + δ) :: w') h hh.2 (Fin.cons e a))
        (∑ l : Fin (j + 1), ((t : ℂ) ^ (l : ℕ)) • Cf l) := by
  classical
  set τ : Fin (j + 1) → ℂ := fun i => (((i : ℕ) : ℝ) : ℂ) with hτdef
  have hτ : Function.Injective τ := by
    intro a b' hab
    simp only [hτdef, Complex.ofReal_inj, Nat.cast_inj] at hab
    exact Fin.ext hab
  set Vi := (Matrix.vandermonde τ)⁻¹ with hVi
  set Vt : Fin (j + 1) → Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp) :=
    fun i a => KB.slv T F j hj ((b, ((i : ℕ) : ℝ) + δ) :: w') h hh.2 (Fin.cons e a) with hVt
  set top : Wd.Ix (Fin w'.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp) :=
    if e = 0 then KB.slv T F j hj w' h hh.2 else 0 with htop
  refine ⟨fun l => if l = Fin.last j then top else ∑ i, Vi l i • Vt i, if_pos rfl, ?_, ?_⟩
  ·
    have hc : ∀ (i : ℕ) (hi : i ≤ r) (hi1 : 1 ≤ i) (w : List C.Letter) (hp : D.IsLocPt h i) (a : Wd.Ix (Fin w.length)),
        KB.CptCoef (T.bs i) (KB.slv T F i hi w h hp.2 a) := fun i hi hi1 w hp a =>
      Formalism.FourierDecayAlt.P.PBE.slice_pos_cpt k r Wp Wq T F hF i hi hi1 w h (by rw [hp.2]) hp a
    intro l
    by_cases hl : l = Fin.last j
    · by_cases he : e = 0
      · simp only [hl, if_pos rfl, htop, he, if_true]
        exact nice_vec_of_cpt (T.bs j) (fun a => hc j hj hj1 w' hh a)
      · simp only [hl, if_pos rfl, htop, he, if_false]
        exact ⟨0, fun a => Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero⟩
    · simp only [hl, if_false]
      refine nice_vec_of_cpt (T.bs j) (fun a => ?_)
      have e1 : (∑ i, Vi l i • Vt i) a = ∑ i, Vi l i • Vt i a := by simp [Finset.sum_apply]
      rw [e1]
      exact cpt_sum (T.bs j) _ _ _ (fun i => hc j hj hj1 _ hh _)
  ·
    intro t a γ hγ
    have hcast : r - j = r - D.ptSize h := by rw [hh.2]
    have hγ' : D.castM hcast γ ∈ B.GV k (r - D.ptSize h) := Formalism.FourierDecayAlt.P.PBE.castM_GV hcast hγ

    have hL := sliceAt_lincomb k r Wp Wq T F hF j hj hj1 h hh Finset.univ
      (fun i => ∑ l : Fin (j + 1), (t : ℂ) ^ (l : ℕ) * Vi l i) (fun i => (b, ((i : ℕ) : ℝ) + δ) :: w')
      (fun _ => Fin.cons e a) (D.uwG k r T.base.z T.base.z' F j hj ((b, t + δ) :: w') (Fin.cons e a)) (by
        intro g hg hD
        obtain ⟨c, -, hc⟩ := hpt a g hg hD
        rw [hc t]
        simp only [hc]
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro m _
        rw [← Finset.sum_smul]
        congr 1
        have := vand_ident τ hτ (t : ℂ) m
        simp only [hτdef] at this
        rw [← this]) (D.castM hcast γ) hγ'

    have hT := sliceAt_lincomb k r Wp Wq T F hF j hj hj1 h hh Finset.univ
      (fun i => Vi (Fin.last j) i) (fun i => (b, ((i : ℕ) : ℝ) + δ) :: w')
      (fun _ => Fin.cons e a) (if e = 0 then D.uwG k r T.base.z T.base.z' F j hj w' a else fun _ => 0) (by
        intro g hg hD
        obtain ⟨c, hcl, hc⟩ := hpt a g hg hD
        simp only [hc]
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        have : ∀ m : Fin (j + 1), ∑ i : Fin (j + 1), (Vi (Fin.last j) i * ((((i : ℕ) : ℝ) : ℂ)) ^ (m : ℕ)) • c m =
            (if Fin.last j = m then (1 : ℂ) else 0) • c m := by
          intro m
          rw [← Finset.sum_smul]
          congr 1
          have := vand_row τ hτ (Fin.last j) m
          simp only [hτdef] at this
          rw [← this]
        simp only [this, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [hcl]
        split_ifs <;> simp) (D.castM hcast γ) hγ'

    show D.castF _ (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' F j hj ((b, t + δ) :: w') (Fin.cons e a)) h) γ = _
    simp only [D.castF]
    rw [hL]
    simp only [Finset.sum_apply, Pi.smul_apply]
    have hR : ∀ x : Fin (j + 1), (if x = Fin.last j then top else ∑ i, Vi x i • Vt i) a γ =
        ∑ q, Vi x q • D.sliceAt k r T.base.z T.base.z'
          (D.uwG k r T.base.z T.base.z' F j hj ((b, ((q : ℕ) : ℝ) + δ) :: w') (Fin.cons e a)) h (D.castM hcast γ) := by
      intro x
      by_cases hx : x = Fin.last j
      · rw [if_pos hx, hx, ← hT]
        simp only [htop]
        by_cases he : e = 0
        · simp only [he, if_true, KB.slv, D.castF]
        · simp only [he, if_false, sliceAt_zero, Pi.zero_apply]
      · rw [if_neg hx]
        simp only [Finset.sum_apply, Pi.smul_apply, hVt, KB.slv, D.castF]
    simp only [hR, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]

end slicepoly

end Formalism.FourierDecayAlt.P.PBG
