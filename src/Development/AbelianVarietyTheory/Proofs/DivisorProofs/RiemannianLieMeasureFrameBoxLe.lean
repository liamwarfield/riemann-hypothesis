module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLiftKodairaSpencerZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfIsIdent
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.FrameBox

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def sgnR {κ : Type} {p q : κ → ℕ} {Ψ : Finset (E →+* ℂ)} (σ : κ ≃ Ψ)
    (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (τ : Ψ) (a : Fin r) : ℝ :=
  if ((e (σ.symm τ)).symm a).isLeft then 1 else -1

def SkewCond {Ψ : Finset (E →+* ℂ)} (d : Ψ → Fin r → ℝ) (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) : Prop :=
  ∀ τ : Ψ, (∑ a, Y (τ, a, a) = 0) ∧
    ∀ a b, Y (τ, b, a) * (d τ b : ℂ) + (d τ a : ℂ) * (starRingEnd ℂ) (Y (τ, a, b)) = 0

def boxEnt (d : Fin r → ℝ) (z a b a' b' : Fin r) : ℂ :=
  if a < b then (if a' = a ∧ b' = b then 1 else if a' = b ∧ b' = a then -((d a * d b : ℝ) : ℂ) else 0)
  else if b < a then
    (if a' = b ∧ b' = a then Complex.I else if a' = a ∧ b' = b then Complex.I * ((d a * d b : ℝ) : ℂ) else 0)
  else (if a' = a ∧ b' = a then Complex.I else if a' = z ∧ b' = z then -Complex.I else 0)


open Classical in
def boxVec {Ψ : Finset (E →+* ℂ)} (d : Ψ → Fin r → ℝ) (z : Fin r) (k : Ψ × {ab : Fin r × Fin r // ab ≠ (z, z)}) :
    EuclideanSpace ℂ (Ψ × Fin r × Fin r) :=
  WithLp.toLp 2 fun m => if m.1 = k.1 then boxEnt (d k.1) z k.2.1.1 k.2.1.2 m.2.1 m.2.2 else 0

def entryL {Ψ : Finset (E →+* ℂ)} (m : Ψ × Fin r × Fin r) : EuclideanSpace ℂ (Ψ × Fin r × Fin r) →ₗ[ℝ] ℂ :=
  ((EuclideanSpace.proj m : EuclideanSpace ℂ (Ψ × Fin r × Fin r) →L[ℂ] ℂ) : _ →ₗ[ℂ] ℂ).restrictScalars ℝ

def boxCoord {Ψ : Finset (E →+* ℂ)} (z : Fin r) (k : Ψ × {ab : Fin r × Fin r // ab ≠ (z, z)}) :
    EuclideanSpace ℂ (Ψ × Fin r × Fin r) →ₗ[ℝ] ℝ :=
  if k.2.1.1 < k.2.1.2 then Complex.reLm ∘ₗ entryL (k.1, k.2.1.1, k.2.1.2)
  else if k.2.1.2 < k.2.1.1 then Complex.imLm ∘ₗ entryL (k.1, k.2.1.2, k.2.1.1)
  else Complex.imLm ∘ₗ entryL (k.1, k.2.1.1, k.2.1.1)

end GlobalTheory.CovTop.VolUp.FrameBox

namespace GlobalTheory.CovTop.VolUp.FrameBox
open Matrix

theorem det_ne_zero_of_isIdent {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (τ : Ψ) : (mat x τ).det ≠ 0 ∧ (G.map τ.1).det ≠ 0 := by
  obtain ⟨h1, h2⟩ := hI (σ.symm τ)
  rw [Equiv.apply_symm_apply] at h1 h2
  set P := permM (e (σ.symm τ)) with hP
  set J := Formalism.UG.Jpq (p (σ.symm τ)) (q (σ.symm τ)) with hJdef
  set M := mat x τ with hMdef
  set B := A (σ.symm τ) with hBdef
  have hPA : (Pᵀ * B) * M = 1 := by rw [Matrix.mul_assoc, h2, transpose_mul_permM]
  have hdetM : M.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hPA
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  refine ⟨hdetM, fun h => ?_⟩
  have hJ : J * J = 1 := by simp [hJdef, Formalism.UG.Jpq, fromBlocks_multiply]
  have hPc : Pᴴ = Pᵀ := by
    ext i j; simp only [hP, permM, conjTranspose_apply, transpose_apply, of_apply]; split_ifs <;> simp
  have hX : Mᴴ * (Bᴴ * J * B) * M = Pᵀ * J * P := by
    rw [← hPc, ← h2, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have hsq : (Pᵀ * J * P) * (Pᵀ * J * P) = 1 := by
    have e1 : (Pᵀ * J * P) * (Pᵀ * J * P) = Pᵀ * J * (P * Pᵀ) * J * P := by simp only [Matrix.mul_assoc]
    rw [e1, permM_mul_transpose, Matrix.mul_one, Matrix.mul_assoc Pᵀ J J, hJ, Matrix.mul_one, transpose_mul_permM]
  have hd0 : (Bᴴ * J * B).det = 0 := by
    rw [h1, det_neg, det_transpose, h, mul_zero]
  have := congrArg Matrix.det hsq
  rw [← hX, det_mul, det_mul, det_mul, hd0] at this
  simp at this

end GlobalTheory.CovTop.VolUp.FrameBox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSkewHermitianBasisVectorEqSqrtTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSkewHermitianBasisVectorEqSqrtTwo
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem boxEnt_norm_sq_eq {r : ℕ} (d : Fin r → ℝ) (hd : ∀ a, d a = 1 ∨ d a = -1) (z a b : Fin r)
    (hab : (a, b) ≠ (z, z)) :
    ∃ P Q : Fin r × Fin r, P ≠ Q ∧ ∀ p : Fin r × Fin r,
      ‖boxEnt d z a b p.1 p.2‖ ^ 2 = (if p = P then 1 else 0) + (if p = Q then 1 else 0) := by
  have hdd : ‖((d a * d b : ℝ) : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    rcases hd a with h | h <;> rcases hd b with h' | h' <;> simp [h, h']
  rcases lt_trichotomy a b with h | h | h
  · refine ⟨(a, b), (b, a), ?_, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; exact h.ne e.1
    · rintro ⟨a', b'⟩
      simp only [boxEnt, if_pos h, Prod.mk.injEq]
      split_ifs <;> (try simp only [norm_neg, norm_mul, hdd, Complex.norm_I, norm_one, norm_zero]) <;> first | (norm_num; done) | (rename_i h1 h2; exact absurd (h1.1.symm.trans h2.1) h.ne)
  · subst h
    have haz : a ≠ z := fun e => hab (by rw [e])
    refine ⟨(a, a), (z, z), ?_, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; exact haz e.1
    · rintro ⟨a', b'⟩
      simp only [boxEnt, lt_irrefl, if_false, Prod.mk.injEq]
      split_ifs <;> simp_all
  · refine ⟨(b, a), (a, b), ?_, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; exact h.ne e.1
    · rintro ⟨a', b'⟩
      simp only [boxEnt, if_neg (not_lt.2 h.le), if_pos h, Prod.mk.injEq]
      split_ifs <;> (try simp only [norm_neg, norm_mul, hdd, Complex.norm_I, norm_one, norm_zero]) <;> first | (norm_num; done) | (rename_i h1 h2; exact absurd (h1.1.symm.trans h2.1) h.ne)

theorem norm_boxVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, ‖boxVec d z k‖ = √2 := by
  intro E _ _ _ r Ψ d z hd k
  obtain ⟨τ, ⟨⟨a, b⟩, hab⟩⟩ := k
  obtain ⟨P, Q, hPQ, hPn⟩ := boxEnt_norm_sq_eq (d τ) (hd τ) z a b hab
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · have : ∀ p : Fin r × Fin r, ‖(boxVec d z ⟨τ, ⟨(a, b), hab⟩⟩) (τ, p)‖ ^ 2 =
        (if p = P then 1 else 0) + (if p = Q then 1 else 0) := by
      intro p
      rw [← hPn p]
      simp [boxVec]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    norm_num
  · intro τ' _ hτ'
    apply Finset.sum_eq_zero
    intro p _
    simp [boxVec, hτ']
  · simp

end GlobalTheory.CovTop.VolUp.FrameBox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSkewHermitianBasisVectorEqSqrtTwoStatement
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_skewHermitianBasisVector_eq_sqrt_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, ‖boxVec d z k‖ = √2 := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.norm_boxVec | exact GlobalTheory.CovTop.VolUp.FrameBox.norm_boxVec | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.norm_boxVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianBasisVectorTraceFreeSkewCond
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianBasisVectorTraceFreeSkewCond
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem sum_boxEnt_diag {r : ℕ} (d : Fin r → ℝ) (z a b : Fin r) (h : (a, b) ≠ (z, z)) :
    ∑ c, boxEnt d z a b c c = 0 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · refine Finset.sum_eq_zero fun c _ => ?_
    have h1 : ¬ (c = a ∧ c = b) := fun hc => hab.ne (hc.1.symm.trans hc.2)
    have h2 : ¬ (c = b ∧ c = a) := fun hc => hab.ne (hc.2.symm.trans hc.1)
    simp only [boxEnt, if_pos hab, if_neg h1, if_neg h2]
  · subst hab
    have haz : a ≠ z := fun hz => h (by rw [hz])
    have : ∀ c, boxEnt d z a a c c = (if c = a then Complex.I else 0) + (if c = z then -Complex.I else 0) := by
      intro c
      simp only [boxEnt, lt_irrefl, if_false, and_self]
      by_cases h1 : c = a
      · subst h1
        simp [haz]
      · simp [h1]
    simp [this, Finset.sum_add_distrib]
  · refine Finset.sum_eq_zero fun c _ => ?_
    have h1 : ¬ (c = a ∧ c = b) := fun hc => hab.ne' (hc.1.symm.trans hc.2)
    have h2 : ¬ (c = b ∧ c = a) := fun hc => hab.ne' (hc.2.symm.trans hc.1)
    simp only [boxEnt, if_pos hab, if_neg hab.not_gt, if_neg h1, if_neg h2]

theorem boxEnt_skew {r : ℕ} (d : Fin r → ℝ) (hd : ∀ a, d a = 1 ∨ d a = -1) (z a b a' b' : Fin r) :
    boxEnt d z a b b' a' * (d b' : ℂ) + (d a' : ℂ) * (starRingEnd ℂ) (boxEnt d z a b a' b') = 0 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hne := hab.ne
    have hne' := hab.ne'
    simp only [boxEnt, if_pos hab]
    by_cases h1 : a' = a ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h1
      rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
    · by_cases h2 : a' = b ∧ b' = a
      · obtain ⟨rfl, rfl⟩ := h2
        rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
      · have h1' : ¬ (b' = b ∧ a' = a) := fun hc => h1 hc.symm
        have h2' : ¬ (b' = a ∧ a' = b) := fun hc => h2 hc.symm
        simp only [if_neg h1, if_neg h2, if_neg h1', if_neg h2']
        simp
  · subst hab
    simp only [boxEnt, lt_irrefl, if_false]
    by_cases h1 : a' = a ∧ b' = a
    · obtain ⟨rfl, rfl⟩ := h1
      simp [mul_comm]
    · have h1' : ¬ (b' = a ∧ a' = a) := fun hc => h1 hc.symm
      simp only [if_neg h1, if_neg h1']
      by_cases h2 : a' = z ∧ b' = z
      · obtain ⟨rfl, rfl⟩ := h2
        simp [mul_comm]
      · have h2' : ¬ (b' = z ∧ a' = z) := fun hc => h2 hc.symm
        simp only [if_neg h2, if_neg h2']
        simp
  · have hne := hab.ne
    have hne' := hab.ne'
    simp only [boxEnt, if_pos hab, if_neg hab.not_gt]
    by_cases h1 : a' = a ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h1
      rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
    · by_cases h2 : a' = b ∧ b' = a
      · obtain ⟨rfl, rfl⟩ := h2
        rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
      · have h1' : ¬ (b' = b ∧ a' = a) := fun hc => h1 hc.symm
        have h2' : ¬ (b' = a ∧ a' = b) := fun hc => h2 hc.symm
        simp only [if_neg h1, if_neg h2, if_neg h1', if_neg h2']
        simp

theorem skewCond_boxVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ))
    (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, SkewCond d (boxVec d z k) := by
  intro E _ _ _ r Ψ d z hd k τ
  by_cases hτ : τ = k.1
  · have he : ∀ a b, boxVec d z k (τ, a, b) = boxEnt (d τ) z k.2.1.1 k.2.1.2 a b := by
      intro a b
      simp only [boxVec, if_pos hτ]
      rw [hτ]
    simp only [he]
    exact ⟨sum_boxEnt_diag _ _ _ _ k.2.2, fun a b => boxEnt_skew _ (hd τ) _ _ _ _ _⟩
  · have he : ∀ a b, boxVec d z k (τ, a, b) = 0 := by
      intro a b
      simp only [boxVec, if_neg hτ]
    simp [he]

end GlobalTheory.CovTop.VolUp.FrameBox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianBasisVectorTraceFreeSkewCondStatement
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitianBasisVector_traceFreeSkewCond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, SkewCond d (boxVec d z k) := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec | exact GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.skewCond_boxVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRealLieIffTraceFreeSkewSigns
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRealLieIffTraceFreeSkewSigns
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

private theorem conj_zero_iff' {R : Type} [Ring R] (a b c d S : R) (hba : b * a = 1) (hcd : c * d = 1) :
    S = 0 ↔ a * S * c = 0 := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  have e : S = b * (a * S * c) * d := by
    simp only [← mul_assoc, hba, one_mul]; rw [mul_assoc, hcd, mul_one]
  rw [e, h]; simp

private theorem expand' {R : Type} [Ring R] (a b c d y z g : R) (hab : a * b = 1) (hdc : d * c = 1) :
    a * (b * (y * a) * g + g * (c * z * d)) * c = y * (a * g * c) + (a * g * c) * z := by
  have : a * (b * (y * a) * g + g * (c * z * d)) * c = (a * b) * y * (a * g * c) + (a * g * c) * z * (d * c) := by
    simp only [mul_add, add_mul, mul_assoc]
  rw [this, hab, hdc, one_mul, mul_one]

private theorem permJ' {r : ℕ} (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin r) :
    (permM e)ᵀ * Formalism.UG.Jpq p q * permM e = diagonal (fun a => if (e.symm a).isLeft then (1:ℂ) else -1) := by
  ext a b
  simp [Matrix.mul_apply, permM, Equiv.apply_eq_iff_eq_symm_apply, diagonal_apply, Formalism.UG.Jpq]
  by_cases hab : a = b
  · subst hab; rw [if_pos rfl]; rcases e.symm a with i | i <;> simp
  · rw [if_neg hab]
    have h := e.symm.injective.ne hab
    revert h
    generalize e.symm a = i
    generalize e.symm b = j
    rcases i with i | i <;> rcases j with j | j <;> intro h <;> simp_all [one_apply]

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem mem_comap_realLie_iff_skewCond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type)
    (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ)
    (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r),
    IsIdent p q Ψ G x σ A e → ∀ Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r),
      Y ∈ (realLie Ψ G).comap (fromFrame x) ↔ SkewCond (sgnR σ e) Y := by
  intro E _ _ _ r κ p q Ψ G x σ A e hI Y
  rw [Submodule.mem_comap, GlobalTheory.SUVol.DensOne.mem_realLie_iff]
  refine forall_congr' fun τ => ?_
  have hdet := (det_ne_zero_of_isIdent hI τ).1
  obtain ⟨h1, h2⟩ := hI (σ.symm τ)
  rw [Equiv.apply_symm_apply] at h1 h2
  set P := permM (e (σ.symm τ)) with hP
  set J := Formalism.UG.Jpq (p (σ.symm τ)) (q (σ.symm τ)) with hJdef
  set M := mat x τ with hMdef
  set B := A (σ.symm τ) with hBdef
  set Gt := G.map τ.1 with hGt
  set Yt : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => Y (τ, a, b) with hYt
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  set N := M⁻¹ with hN
  have hMN : M * N = 1 := Matrix.mul_nonsing_inv M hu
  have hNM : N * M = 1 := Matrix.nonsing_inv_mul M hu
  have hX : Matrix.of (fromFrame x Y τ) = M * Yt * N := rfl
  rw [hX]
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal (fun a => ((sgnR σ e τ a : ℝ) : ℂ)) with hD
  have hPJP : Pᵀ * J * P = D := by
    rw [hP, hJdef, permJ', hD]
    congr 1; funext a; simp only [sgnR]; split_ifs <;> simp
  have hPc : Pᴴ = Pᵀ := by
    ext i j; simp only [hP, permM, conjTranspose_apply, transpose_apply, of_apply]; split_ifs <;> simp
  have hMt : (Mᴴ)ᵀ = M.map (starRingEnd ℂ) := by ext i j; simp
  have hG' : Gt = -(Bᴴ * J * B)ᵀ := by rw [h1, transpose_neg, transpose_transpose, neg_neg]
  have hH : Mᵀ * Gt * M.map (starRingEnd ℂ) = -D := by
    rw [hG', ← hMt, Matrix.mul_neg, Matrix.neg_mul]
    rw [show Mᵀ * (Bᴴ * J * B)ᵀ * (Mᴴ)ᵀ = (Mᴴ * (Bᴴ * J * B) * M)ᵀ by simp only [transpose_mul, Matrix.mul_assoc]]
    have : Mᴴ * (Bᴴ * J * B) * M = Pᵀ * J * P := by
      rw [← hPc, ← h2, conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [this, hPJP, hD, diagonal_transpose]
  have hc1 : M.map (starRingEnd ℂ) * N.map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc2 : N.map (starRingEnd ℂ) * M.map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  have ht1 : Mᵀ * Nᵀ = 1 := by rw [← transpose_mul, hNM, transpose_one]
  have ht2 : Nᵀ * Mᵀ = 1 := by rw [← transpose_mul, hMN, transpose_one]
  have htr : (M * Yt * N).trace = ∑ a, Y (τ, a, a) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, hNM, Matrix.one_mul]; rfl
  rw [htr, and_comm]
  refine and_congr_right fun _ => ?_
  rw [conj_zero_iff' Mᵀ Nᵀ (M.map (starRingEnd ℂ)) (N.map (starRingEnd ℂ)) _ ht2 hc1]
  rw [transpose_mul, transpose_mul, Matrix.map_mul, Matrix.map_mul]
  rw [expand' _ _ _ _ _ _ _ ht1 hc2, hH]
  rw [Matrix.mul_neg, Matrix.neg_mul, ← neg_add, neg_eq_zero, ← Matrix.ext_iff]
  refine forall_congr' fun a => forall_congr' fun b => ?_
  rw [eq_comm (b := (0 : Matrix (Fin r) (Fin r) ℂ) a b)]
  simp [hD, hYt, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact eq_comm

end GlobalTheory.CovTop.VolUp.FrameBox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRealLieIffTraceFreeSkewSignsStatement
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_realLie_iff_traceFree_skew_signs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), IsIdent p q Ψ G x σ A e → ∀ Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r), Y ∈ (realLie Ψ G).comap (fromFrame x) ↔ SkewCond (sgnR σ e) Y := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.mem_comap_realLie_iff_skewCond | exact GlobalTheory.CovTop.VolUp.FrameBox.mem_comap_realLie_iff_skewCond | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.mem_comap_realLie_iff_skewCond <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCoordinateDualBasisVector
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCoordinateDualBasisVector
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox
open Classical

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem boxCoord_boxVec (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ))
    (d : Ψ → Fin r → ℝ) (z : Fin r) (_hd : ∀ τ a, d τ a = 1 ∨ d τ a = -1) :
    ∀ j k, boxCoord z j (boxVec d z k) = if j = k then 1 else 0 := by
  rintro ⟨τ', ⟨⟨a', b'⟩, hj⟩⟩ ⟨τ, ⟨⟨a, b⟩, hk⟩⟩
  have hjk : ((τ', (⟨(a', b'), hj⟩ : {ab : Fin r × Fin r // ab ≠ (z, z)})) =
      (τ, (⟨(a, b), hk⟩ : {ab : Fin r × Fin r // ab ≠ (z, z)}))) ↔ τ' = τ ∧ a' = a ∧ b' = b := by
    constructor
    · intro h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact ⟨h.1, h.2.1, h.2.2⟩
    · rintro ⟨rfl, rfl, rfl⟩; rfl
  simp only [hjk]
  simp only [boxCoord, boxVec, LinearMap.coe_comp, Function.comp_apply, Complex.reLm_coe, Complex.imLm_coe]
  simp only [entryL, LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe, EuclideanSpace.proj, PiLp.toLp_apply]
  by_cases hτ : τ' = τ
  swap
  · split_ifs <;> simp_all
  subst hτ
  simp only [true_and, if_true]
  clear hjk
  split_ifs with h1 h1' h3 h3 h3 h3 h3 h3
  all_goals simp only [LinearMap.coe_comp, Function.comp_apply, Complex.reLm_coe, Complex.imLm_coe, entryL, LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe, EuclideanSpace.proj, PiLp.toLp_apply, PiLp.proj_apply, boxEnt, if_true]
  all_goals rcases lt_trichotomy a b with h2 | rfl | h2
  all_goals (try simp only [lt_irrefl, if_false])
  all_goals (try simp only [h2, not_lt_of_gt h2, if_true, if_false])
  all_goals clear _hd
  all_goals (split_ifs with e1 e2 <;> (try obtain ⟨rfl, rfl⟩ := h1') <;> (try obtain ⟨rfl, rfl⟩ := e1) <;> (try obtain ⟨rfl, rfl⟩ := e2) <;> (try simp))
  all_goals (try (simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff, Prod.ext_iff, ne_eq, Prod.mk.injEq] at *; omega))
  all_goals exact absurd ⟨rfl, rfl⟩ h3

end GlobalTheory.CovTop.VolUp.FrameBox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCoordinateDualBasisVectorStatement
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitianCoordinate_dual_basisVector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ j k, boxCoord z j (boxVec d z k) = if j = k then 1 else 0 := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.boxCoord_boxVec | exact GlobalTheory.CovTop.VolUp.FrameBox.boxCoord_boxVec | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.boxCoord_boxVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeCoordinateBoxLeHadamard
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeCoordinateBoxLeHadamard
open MeasureTheory

namespace GlobalTheory.CoordBox

theorem volume_coordBox_le (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (K : Type) [Fintype K]
    (w : K → V) (t : ℝ) (ht : 0 ≤ t) (hK : Fintype.card K = Module.finrank ℝ V) :
    MeasureTheory.volume {y : V | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k}
      ≤ ENNReal.ofReal ((2 * t) ^ Fintype.card K * ∏ k, ‖w k‖) := by
  classical
  set n := Fintype.card K with hn
  let o : OrthonormalBasis K ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (Fintype.equivFinOfCardEq hK).symm
  let v : K → V := fun k => (2 * t) • w k
  let a : V := -∑ k, t • w k
  have hsub : {y : V | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k}
      ⊆ (fun x => x + a) '' parallelepiped v := by
    rintro y ⟨c, hc, rfl⟩
    set s : K → ℝ := fun k => (c k + t) / (2 * t) with hs
    have hkey : ∀ k, s k * (2 * t) = c k + t := by
      intro k
      rcases ht.eq_or_lt with h0 | hpos
      · have hck : c k = 0 := by
          have := hc k
          rw [← h0] at this
          exact abs_nonpos_iff.mp this
        simp [hs, ← h0, hck]
      · simp only [hs]
        field_simp
    refine ⟨∑ k, s k • v k, ?_, ?_⟩
    · rw [mem_parallelepiped_iff]
      refine ⟨s, ?_, rfl⟩
      constructor
      · intro k
        have h1 := (abs_le.mp (hc k)).1
        exact div_nonneg (by linarith) (by linarith)
      · intro k
        have h2 := (abs_le.mp (hc k)).2
        exact div_le_one_of_le₀ (by linarith) (by linarith)
    · simp only [v, a, smul_smul, hkey, add_smul, Finset.sum_add_distrib]
      abel
  have hvol : volume (parallelepiped v) = ENNReal.ofReal ((2 * t) ^ n * |o.toBasis.det w|) := by
    rw [← o.addHaar_eq_volume, MeasureTheory.Measure.addHaar_parallelepiped]
    congr 1
    have hsm : o.toBasis.det v = (∏ _k : K, (2 * t)) • o.toBasis.det w :=
      o.toBasis.det.toMultilinearMap.map_smul_univ (fun _ => 2 * t) w
    rw [hsm, Finset.prod_const, Finset.card_univ, smul_eq_mul, abs_mul, abs_pow,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * t)]
  have hdet : |o.toBasis.det w| ≤ ∏ k, ‖w k‖ := by
    have := GlobalTheory.Hadamard.norm_orthonormalBasis_det_le (𝕜 := ℝ) o w
    simpa [Real.norm_eq_abs] using this
  calc volume {y : V | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k}
      ≤ volume ((fun x => x + a) '' parallelepiped v) := measure_mono hsub
    _ = volume (parallelepiped v) := by
        rw [Set.image_add_right, measure_preimage_add_right]
    _ = ENNReal.ofReal ((2 * t) ^ n * |o.toBasis.det w|) := hvol
    _ ≤ ENNReal.ofReal ((2 * t) ^ Fintype.card K * ∏ k, ‖w k‖) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left hdet (pow_nonneg (by linarith) _)

end GlobalTheory.CoordBox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeCoordinateBoxLeHadamardStatement
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_coordinateBox_le_hadamard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (K : Type) [Fintype K] (w : K → V) (t : ℝ), 0 ≤ t → Fintype.card K = Module.finrank ℝ V → MeasureTheory.volume {y : V | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k} ≤ ENNReal.ofReal ((2 * t) ^ Fintype.card K * ∏ k, ‖w k‖) := by
  first | exact @GlobalTheory.CoordBox.volume_coordBox_le | exact GlobalTheory.CoordBox.volume_coordBox_le | (intros; apply GlobalTheory.CoordBox.volume_coordBox_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxLe
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.FrameBox
open Matrix

theorem riemLie_frameBox_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), 1 ≤ r → IsIdent p q Ψ G x σ A e → ∀ t : ℝ, 0 < t → riemLie Ψ G x {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < t} ≤ ENNReal.ofReal ((3 * t) ^ (Ψ.card * (r ^ 2 - 1))) := by
  classical
  intro E _ _ _ r κ p q Ψ G x σ A e hr hI t ht
  set W := (realLie Ψ G).comap (fromFrame x) with hW
  set z : Fin r := ⟨0, hr⟩ with hz
  set d := sgnR σ e with hd_def
  have hd : ∀ τ a, d τ a = 1 ∨ d τ a = -1 := fun τ a => by
    simp only [d, sgnR]; split_ifs <;> simp
  have hinv := det_ne_zero_of_isIdent hI
  have hvW : ∀ k, boxVec d z k ∈ W := fun k =>
    (GlobalTheory.T.mem_realLie_iff_traceFree_skew_signs E r κ p q Ψ G x σ A e hI _).2 (GlobalTheory.T.skewHermitianBasisVector_traceFreeSkewCond E r Ψ d z hd k)
  let K := Ψ × {ab : Fin r × Fin r // ab ≠ (z, z)}
  let w : K → W := fun k => ⟨boxVec d z k, hvW k⟩
  have hdual := GlobalTheory.T.skewHermitianCoordinate_dual_basisVector E r Ψ d z hd
  have hcoord : ∀ (g : K → ℝ) j, boxCoord z j ((∑ k, g k • w k : W) : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = g j := by
    intro g j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, w, hdual, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_eq_single j (fun k hk => by rw [if_neg (Ne.symm hk)])]
    rw [if_pos rfl]
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := hcoord g j
    rw [hg] at this
    simpa using this.symm
  have hcardK : Fintype.card K = Ψ.card * (r ^ 2 - 1) := by
    simp [K, Fintype.card_prod, Fintype.card_coe, sq]
  have hfin : Fintype.card K = Module.finrank ℝ W := by
    refine le_antisymm hli.fintype_card_le_finrank ?_
    rw [hcardK]
    rcases Ψ.eq_empty_or_nonempty with h0 | ⟨τ0, hτ0⟩
    · have hs : Subsingleton W := ⟨fun a b => Subtype.ext (PiLp.ext fun m => by
        have := m.1.2; simp [h0] at this)⟩
      rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _
    · have hG : G.det ≠ 0 := by
        intro h
        apply (hinv ⟨τ0, hτ0⟩).2
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
      exact finrank_comap_realLie_le Ψ G x hr hG fun τ => (hinv τ).1
  have hspan : Submodule.span ℝ (Set.range w) = ⊤ := hli.span_eq_top_of_card_eq_finrank' hfin
  have hrep : ∀ Y : W, Y = ∑ k, boxCoord z k (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) • w k := by
    intro Y
    have hYs : Y ∈ Submodule.span ℝ (Set.range w) := hspan ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 hYs
    have h2 : ∀ j, boxCoord z j (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = c j := by
      intro j
      rw [← hc]
      exact hcoord _ j
    simp_rw [h2]; exact hc.symm
  set S := {X : Ψ → Fin r → Fin r → ℂ | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < t} with hS_def
  have hSo : IsOpen S := by
    simp only [hS_def, Set.setOf_forall]
    refine isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => isOpen_lt ?_ continuous_const
    have : Continuous fun X : Ψ → Fin r → Fin r → ℂ => Matrix.of (X τ) := continuous_apply τ
    exact (((continuous_const.matrix_mul this).matrix_mul continuous_const).matrix_elem a b).norm
  have hf : Measurable (fun Y : W => fromFrame x Y.1) :=
    ((fromFrame x).comp W.subtype).continuous_of_finiteDimensional.measurable
  unfold riemLie
  rw [Measure.map_apply hf hSo.measurableSet, OrthonormalBasis.addHaar_eq_volume]
  have key1 : ∀ τ (M : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * M * (mat x τ)⁻¹) * mat x τ = M := fun τ M => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hinv τ).1.isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hinv τ).1.isUnit]
  have hsub : (fun Y : W => fromFrame x Y.1) ⁻¹' S ⊆
      {y : W | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k} := by
    intro Y hY
    have hY' : ∀ τ a b, ‖(Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (τ, a, b)‖ < t := by
      intro τ a b
      have := hY τ a b
      have e1 : Matrix.of (fromFrame x Y.1 τ) =
          mat x τ * Matrix.of (fun a b => (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (τ, a, b)) * (mat x τ)⁻¹ := rfl
      rwa [e1, key1] at this
    refine ⟨fun k => boxCoord z k (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)), fun k => ?_, hrep Y⟩
    obtain ⟨τ, ⟨⟨a, b⟩, hab⟩⟩ := k
    simp only [boxCoord]
    split_ifs
    · exact (Complex.abs_re_le_norm _).trans (hY' _ _ _).le
    · exact (Complex.abs_im_le_norm _).trans (hY' _ _ _).le
    · exact (Complex.abs_im_le_norm _).trans (hY' _ _ _).le
  refine (measure_mono hsub).trans ((GlobalTheory.T.volume_coordinateBox_le_hadamard W K w t ht.le hfin).trans (ENNReal.ofReal_le_ofReal ?_))
  have hn : ∀ k, ‖w k‖ = √2 := fun k => GlobalTheory.T.norm_skewHermitianBasisVector_eq_sqrt_two E r Ψ d z hd k
  simp only [hn, Finset.prod_const, Finset.card_univ]
  rw [hcardK, ← mul_pow]
  have h2 : 2 * t * √2 ≤ 3 * t := by
    have hs : √2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith
  exact pow_le_pow_left₀ (by positivity) h2 _

end GlobalTheory.CovTop.VolUp.FrameBox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxLeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianLieMeasure_frameBox_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), 1 ≤ r → IsIdent p q Ψ G x σ A e → ∀ t : ℝ, 0 < t → riemLie Ψ G x {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < t} ≤ ENNReal.ofReal ((3 * t) ^ (Ψ.card * (r ^ 2 - 1))) := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.riemLie_frameBox_le | exact GlobalTheory.CovTop.VolUp.FrameBox.riemLie_frameBox_le | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.riemLie_frameBox_le <;> assumption)
end
