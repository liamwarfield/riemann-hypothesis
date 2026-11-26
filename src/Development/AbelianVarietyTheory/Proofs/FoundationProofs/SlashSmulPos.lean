module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlSemisimpleOnLOldSpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlSqSubMemOldformsGamma1
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusOldformTraceToGammaZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusOldformTraceToGammaZero
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.TrOld

def rep (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : Option (Fin l) → SL(2, ℤ)
  | none => 1
  | some j => gaOld N l a b h j

def sig (l : ℕ) [NeZero l] (x : SL(2, ℤ)) : Option (Fin l) :=
  if (l : ℤ) ∣ mat x 1 0 then none
  else some ⟨(((mat x 1 1 : ℤ) : ZMod l) * ((mat x 1 0 : ℤ) : ZMod l)⁻¹).val, ZMod.val_lt _⟩

lemma mul_11 (x y : SL(2, ℤ)) : mat (x * y) 1 1 = mat x 1 0 * mat y 0 1 + mat x 1 1 * mat y 1 1 := by
  simp only [mat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

lemma mulInv_10 (x y : SL(2, ℤ)) : mat (x * y⁻¹) 1 0 = mat x 1 0 * mat y 1 1 - mat x 1 1 * mat y 1 0 := by
  simp [mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ring

lemma mulInv_11 (x y : SL(2, ℤ)) : mat (x * y⁻¹) 1 1 = -(mat x 1 0 * mat y 0 1) + mat x 1 1 * mat y 0 0 := by
  simp [mat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

lemma mem_iff (M : ℕ) (x : SL(2, ℤ)) : x ∈ Gamma0 M ↔ (M : ℤ) ∣ mat x 1 0 := by
  rw [Gamma0_mem]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

section
variable {N l : ℕ} {a b : ℤ} {h : (l : ℤ) * b - N * a = 1}

lemma rep_none_10 : mat (rep N l a b h none) 1 0 = 0 := rfl
lemma rep_none_11 : mat (rep N l a b h none) 1 1 = 1 := rfl
lemma rep_some_10 (j : Fin l) : mat (rep N l a b h (some j)) 1 0 = N := rfl
lemma rep_some_11 (j : Fin l) : mat (rep N l a b h (some j)) 1 1 = (N : ℤ) * (j : ℕ) + l * b := rfl

lemma rep_00 (o : Option (Fin l)) : mat (rep N l a b h o) 0 0 = 1 := by
  cases o <;> simp [rep, gaOld, mat]

lemma rep_10 (o : Option (Fin l)) : ((mat (rep N l a b h o) 1 0 : ℤ) : ZMod N) = 0 := by
  cases o with
  | none => rw [rep_none_10]; simp
  | some j => rw [rep_some_10]; simp

lemma rep_11 (o : Option (Fin l)) : ((mat (rep N l a b h o) 1 1 : ℤ) : ZMod N) = 1 := by
  cases o with
  | none => rw [rep_none_11]; simp
  | some j =>
    have hc := congrArg (Int.cast : ℤ → ZMod N) h
    push_cast at hc
    rw [ZMod.natCast_self, zero_mul, sub_zero] at hc
    rw [rep_some_11]
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add, hc]

include h in
lemma cop : IsCoprime (N : ℤ) (l : ℤ) := ⟨-a, b, by linear_combination h⟩

lemma sig_mem [NeZero l] (hl : l.Prime) (x : SL(2, ℤ)) (hx : x ∈ Gamma0 N) :
    x * (rep N l a b h (sig l x))⁻¹ ∈ Gamma0 (N * l) := by
  have := Fact.mk hl
  have hc : IsCoprime (N : ℤ) l := cop (h := h)
  have hδ : ∀ o, (N : ℤ) ∣ mat (rep N l a b h o) 1 0 := fun o =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (rep_10 o)
  rw [mem_iff] at hx
  rw [mem_iff, mulInv_10]
  push_cast
  apply hc.mul_dvd
  · exact dvd_sub (Dvd.dvd.mul_right hx _) (Dvd.dvd.mul_left (hδ _) _)
  · unfold sig
    split_ifs with hd
    · rw [rep_none_10, rep_none_11]
      simpa using hd
    · rw [rep_some_10, rep_some_11, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hc0 : ((mat x 1 0 : ℤ) : ZMod l) ≠ 0 := by
        rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hu := mul_inv_cancel₀ hc0
      have hl0 : ((l : ℕ) : ZMod l) = 0 := ZMod.natCast_self l
      push_cast
      simp only [ZMod.natCast_zmod_val]
      linear_combination ((N : ZMod l) * ((mat x 1 1 : ℤ) : ZMod l)) * hu +
        (((mat x 1 0 : ℤ) : ZMod l) * (b : ZMod l)) * hl0

lemma not_dvd (hN : 0 < N) (hl : l.Prime) : ¬ ((N : ℤ) * l ∣ N) := by
  intro hd
  have h1 := Int.le_of_dvd (by exact_mod_cast hN) hd
  have h2 : (2 : ℤ) ≤ l := by exact_mod_cast hl.two_le
  have h3 : (0 : ℤ) < N := by exact_mod_cast hN
  nlinarith

lemma rep_inj (hN : 0 < N) (hl : l.Prime) (o₁ o₂ : Option (Fin l))
    (hm : rep N l a b h o₁ * (rep N l a b h o₂)⁻¹ ∈ Gamma0 (N * l)) : o₁ = o₂ := by
  have hc : IsCoprime (N : ℤ) l := cop (h := h)
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  rw [mem_iff, mulInv_10] at hm
  push_cast at hm
  rcases o₁ with _ | i <;> rcases o₂ with _ | j
  · rfl
  · exfalso
    rw [rep_none_10, rep_none_11, rep_some_10] at hm
    exact not_dvd hN hl (by simpa using hm)
  · exfalso
    rw [rep_some_10, rep_none_11, rep_none_10] at hm
    exact not_dvd hN hl (by simpa using hm)
  · rw [rep_some_10, rep_some_11, rep_some_10, rep_some_11] at hm
    have e : (N : ℤ) * (N * (j : ℕ) + l * b) - (N * (i : ℕ) + l * b) * N =
        N * (N * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))) := by ring
    rw [e] at hm
    have h1 : (l : ℤ) ∣ N * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) := (mul_dvd_mul_iff_left hN'.ne').1 hm
    have h2 : (l : ℤ) ∣ ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := hc.symm.dvd_of_dvd_mul_left h1
    have h3 : ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd h2
      have := i.isLt
      have := j.isLt
      rw [abs_lt]
      constructor <;> omega
    congr 1
    ext
    omega

end

end GlobalTheory.HeckeFamilyMatrices.TrOld


open GlobalTheory.HeckeFamilyMatrices.TrOld in
theorem GlobalTheory.HeckeFamilyMatrices.chiInv_trOld : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1)
    (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < N → l.Prime → ChiInv k N (N * l) χ G →
    ChiInv k N N χ (trOld k N l a b h G) := by
  intro N l k a b h χ G hN hl hG γ hγ
  have : NeZero l := ⟨hl.ne_zero⟩
  have rep_mem : ∀ o, rep N l a b h o ∈ Gamma0 N := fun o => Gamma0_mem.2 (rep_10 o)
  have hsum : trOld k N l a b h G = ∑ o : Option (Fin l), G ∣[k] rep N l a b h o := by
    rw [Fintype.sum_option]
    simp only [rep, SlashAction.slash_one]
    unfold trOld
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun j => G ∣[k] gaOld N l a b h j) l).symm
  have hterm : ∀ o, (G ∣[k] rep N l a b h o) ∣[k] γ =
      χ ((mat γ 1 1 : ℤ) : ZMod N) • (G ∣[k] rep N l a b h (sig l (rep N l a b h o * γ))) := by
    intro o
    have hA : rep N l a b h o * γ ∈ Gamma0 N := mul_mem (rep_mem o) hγ
    have hη := sig_mem (h := h) hl _ hA
    have hA0 : ((mat (rep N l a b h o * γ) 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.1 hA
    have hchar : ((mat (rep N l a b h o * γ * (rep N l a b h (sig l (rep N l a b h o * γ)))⁻¹) 1 1 : ℤ)
        : ZMod N) = ((mat γ 1 1 : ℤ) : ZMod N) := by
      rw [mulInv_11, rep_00]
      push_cast
      rw [hA0, mul_11]
      push_cast
      rw [rep_10, rep_11]
      ring
    have e : G ∣[k] (rep N l a b h o * γ) =
        (G ∣[k] (rep N l a b h o * γ * (rep N l a b h (sig l (rep N l a b h o * γ)))⁻¹)) ∣[k]
          rep N l a b h (sig l (rep N l a b h o * γ)) := by
      rw [← SlashAction.slash_mul, inv_mul_cancel_right]
    rw [← SlashAction.slash_mul, e, hG _ hη, ModularForm.SL_smul_slash, hchar]
  have hinj : Function.Injective (fun o => sig l (rep N l a b h o * γ)) := by
    intro o₁ o₂ he
    apply rep_inj (h := h) hN hl
    have h1 := sig_mem (h := h) hl _ (mul_mem (rep_mem o₁) hγ)
    have h2 := sig_mem (h := h) hl _ (mul_mem (rep_mem o₂) hγ)
    simp only at he
    rw [he] at h1
    have h3 := mul_mem h1 (inv_mem h2)
    convert h3 using 1
    group
  rw [hsum, SlashAction.sum_slash, Finset.sum_congr rfl (fun o _ => hterm o), ← Finset.smul_sum]
  congr 1
  exact (Finite.injective_iff_bijective.mp hinj).sum_comp (fun o => G ∣[k] rep N l a b h o)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusOldformTraceToGammaZeroStatement
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nebentypus_oldformTraceToGammaOne : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < N → l.Prime → ChiInv k N (N * l) χ G → ChiInv k N N χ (trOld k N l a b h G) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.chiInv_trOld | exact GlobalTheory.HeckeFamilyMatrices.chiInv_trOld | (intros; apply GlobalTheory.HeckeFamilyMatrices.chiInv_trOld <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusSlashOldformLevelRaisingMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusSlashOldformLevelRaisingMatrix
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

def wConjMat (N l a b p q t s : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![l * b * p + a * b * (N * l * t) - N * l * q - N * a * s, -a * p - a ^ 2 * N * t + l * q + a * s;
    N * l * (b * p + l * b ^ 2 * t - N * q - b * s), -N * a * p - a * b * (N * l * t) + N * l * q + l * b * s]

lemma wConjMat_det (N l a b p q t s : ℤ) (hab : l * b - N * a = 1) (hd : p * s - q * (N * l * t) = 1) :
    (wConjMat N l a b p q t s).det = 1 := by
  rw [wConjMat, Matrix.det_fin_two_of]
  linear_combination (l * b - N * a) ^ 2 * hd + (l * b - N * a + 1) * hab

lemma wOld_mul_eq (N l : ℕ) (a b p q t s : ℤ) (hab : (l : ℤ) * b - N * a = 1) :
    wOld N l a b * !![p, q; (N : ℤ) * l * t, s] = wConjMat N l a b p q t s * wOld N l a b := by
  rw [wOld, wConjMat, Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (-((l : ℤ) * p + a * (N * l * t))) * hab
  · linear_combination (-((l : ℤ) * q + a * s)) * hab
  · linear_combination (-((N : ℤ) * l * p + l * b * (N * l * t))) * hab
  · linear_combination (-((N : ℤ) * l * q + l * b * s)) * hab

theorem chiInv_slash_wOld : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ), (l : ℤ) * b - N * a = 1 →
    ∀ (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < l → ChiInv k N (N * l) χ G →
      ChiInv k N (N * l) χ (G ∣[k] toGL (wOld N l a b)) := by
  intro N l k a b hab χ G hl hG γ hγ
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  obtain ⟨t, ht⟩ := hγ
  have ht' : mat γ 1 0 = (N : ℤ) * l * t := by rw [← Nat.cast_mul]; exact ht
  have hm : mat γ = !![mat γ 0 0, mat γ 0 1; (N : ℤ) * l * t, mat γ 1 1] := by
    rw [← ht']; exact Matrix.eta_fin_two _
  have hd : mat γ 0 0 * mat γ 1 1 - mat γ 0 1 * ((N : ℤ) * l * t) = 1 := by
    rw [← ht', ← Matrix.det_fin_two]; exact γ.2
  let δ : SL(2, ℤ) := ⟨wConjMat N l a b (mat γ 0 0) (mat γ 0 1) t (mat γ 1 1),
    wConjMat_det _ _ _ _ _ _ _ _ hab hd⟩
  have hδ : mat δ = wConjMat N l a b (mat γ 0 0) (mat γ 0 1) t (mat γ 1 1) := rfl
  have key : wOld N l a b * mat γ = mat δ * wOld N l a b := by
    rw [hδ, ← wOld_mul_eq N l a b _ _ t _ hab, ← hm]
  have hW : 0 < (wOld N l a b).det := by
    have : (wOld N l a b).det = l := by
      rw [wOld, Matrix.det_fin_two_of]; linear_combination (l : ℤ) * hab
    rw [this]; exact_mod_cast hl
  have h1 : ∀ x : SL(2, ℤ), (mat x).det ≠ 0 := fun x => by simp [mat]
  have hδ0 : δ ∈ Gamma0 (N * l) := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨b * mat γ 0 0 + l * b ^ 2 * t - N * mat γ 0 1 - b * mat γ 1 1, ?_⟩
    rw [Nat.cast_mul]; rfl
  have h11 : ((mat δ 1 1 : ℤ) : ZMod N) = ((mat γ 1 1 : ℤ) : ZMod N) := by
    have : mat δ 1 1 = mat γ 1 1 +
        N * (-a * mat γ 0 0 - a * b * l * t + l * mat γ 0 1 + a * mat γ 1 1) := by
      have e : mat δ 1 1 = -(N : ℤ) * a * mat γ 0 0 - a * b * (N * l * t) + N * l * mat γ 0 1 +
        l * b * mat γ 1 1 := rfl
      rw [e]; linear_combination (mat γ 1 1) * hab
    rw [this, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]
  rw [slash_SL_eq, ← SlashAction.slash_mul, ← toGL_mul _ _ hW.ne' (h1 γ), key,
    toGL_mul _ _ (h1 δ) hW.ne', SlashAction.slash_mul, ← slash_SL_eq, hG δ hδ0,
    smul_slash_toGL k _ hW, h11]

end GlobalTheory.HeckeFamilyMatrices
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusSlashOldformLevelRaisingMatrixStatement
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nebentypus_slash_oldformLevelRaisingMatrix : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ), (l : ℤ) * b - N * a = 1 → ∀ (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < l → ChiInv k N (N * l) χ G → ChiInv k N (N * l) χ (G ∣[k] toGL (wOld N l a b)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.chiInv_slash_wOld | exact GlobalTheory.HeckeFamilyMatrices.chiInv_slash_wOld | (intros; apply GlobalTheory.HeckeFamilyMatrices.chiInv_slash_wOld <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusSlashIntDiagTwoMatrixLevelRaise
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusSlashIntDiagTwoMatrixLevelRaise
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem chiInv_slash_dg (N l : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ) (hl : 0 < l)
    (hB : ChiInv k N N χ B) : ChiInv k N (N * l) χ (B ∣[k] toGL (dg l 1)) := by
  intro γ hγ
  rw [Gamma0_mem] at hγ
  have hdvd : ((N * l : ℕ) : ℤ) ∣ (mat γ 1 0) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ
  obtain ⟨t, ht⟩ := hdvd
  have hdet : (mat γ).det = 1 := by simp [mat]
  rw [Matrix.det_fin_two] at hdet
  let γ' : SL(2, ℤ) := ⟨!![mat γ 0 0, (l : ℤ) * mat γ 0 1; (N : ℤ) * t, mat γ 1 1], by
    rw [Matrix.det_fin_two_of]; push_cast at ht; rw [ht] at hdet; linear_combination hdet⟩
  have hE : γ' ∈ Gamma0 N := by
    rw [Gamma0_mem]; simp [γ']
  have hD : (dg l 1).det ≠ 0 := by simp [dg, Matrix.det_fin_two_of]; omega
  have hDpos : 0 < (dg l 1).det := by simp [dg, Matrix.det_fin_two_of]; exact_mod_cast hl
  have hγd : (mat γ).det ≠ 0 := by simp [mat]
  have hEd : (mat γ').det ≠ 0 := by simp [mat]
  have hmul : dg l 1 * mat γ = mat γ' * dg l 1 := by
    push_cast at ht
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [dg, γ', mat, Matrix.mul_apply, Fin.sum_univ_two, ht] <;> ring
  have hs : mat γ' 1 1 = mat γ 1 1 := rfl
  rw [slash_SL_eq, ← SlashAction.slash_mul, ← toGL_mul _ _ hD hγd, hmul, toGL_mul _ _ hEd hD,
    SlashAction.slash_mul, ← slash_SL_eq, hB γ' hE, smul_slash_toGL k _ hDpos, hs]

end GlobalTheory.HeckeFamilyMatrices
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusSlashIntDiagTwoMatrixLevelRaiseStatement
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nebentypus_slash_intDiagTwoMatrix_levelRaise : ∀ (N l : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ), 0 < l → ChiInv k N N χ B → ChiInv k N (N * l) χ (B ∣[k] toGL (dg l 1)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.chiInv_slash_dg | exact GlobalTheory.HeckeFamilyMatrices.chiInv_slash_dg | (intros; apply GlobalTheory.HeckeFamilyMatrices.chiInv_slash_dg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OldformLevelRaisingSlashSlashNebentypus
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OldformLevelRaisingSlashSlashNebentypus
noncomputable section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

def wSqOld (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : SL(2, ℤ) :=
  ⟨!![(l : ℤ) + a * N, a * (1 + b); (N : ℤ) * l * (1 + b), (N : ℤ) * a + l * b ^ 2], by
    rw [Matrix.det_fin_two_of]; linear_combination ((l : ℤ) * b - N * a + 1) * h⟩

lemma oldformLevelRaisingMatrix_det_eq_level (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : (wOld N l a b).det = l := by
  rw [wOld, Matrix.det_fin_two_of]; linear_combination (l : ℤ) * h

lemma atkin_lehner_square_mul (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) :
    wOld N l a b * wOld N l a b = (l : ℤ) • mat (wSqOld N l a b h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wOld, wSqOld, mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma wSqOld_mem (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) :
    wSqOld N l a b h ∈ Gamma0 (N * l) := by
  rw [Gamma0_mem]
  have : ((((wSqOld N l a b h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ)) = ((N * l : ℕ) : ℤ) * (1 + b) := by
    simp [wSqOld]
  rw [this, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

lemma wSqOld_entry (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) :
    ((mat (wSqOld N l a b h) 1 1 : ℤ) : ZMod N) = (b : ZMod N) := by
  have e : mat (wSqOld N l a b h) 1 1 = b + (N : ℤ) * (a * (1 + b)) := by
    simp [wSqOld, mat]; linear_combination b * h
  rw [e]; push_cast; simp

theorem wOld_slash_slash (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (χ : DirichletCharacter ℂ N)
    (G : ℍ → ℂ) (hl : 0 < l) (hG : ChiInv k N (N * l) χ G) :
    (G ∣[k] toGL (wOld N l a b)) ∣[k] toGL (wOld N l a b) = ((l : ℂ) ^ (k - 2) * χ (b : ZMod N)) • G := by
  have hd : (wOld N l a b).det ≠ 0 := by rw [oldformLevelRaisingMatrix_det_eq_level N l a b h]; exact_mod_cast hl.ne'
  have hM : 0 < (mat (wSqOld N l a b h)).det := by simp [mat]
  rw [← SlashAction.slash_mul, ← toGL_mul _ _ hd hd, atkin_lehner_square_mul N l a b h, slash_toGL_smul k l hl _ hM,
    ← slash_SL_eq, hG _ (wSqOld_mem N l a b h), wSqOld_entry, smul_smul]

end GlobalTheory.HeckeFamilyMatrices
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OldformLevelRaisingSlashSlashNebentypusStatement
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oldformLevelRaising_slash_slash_nebentypus : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ), (l : ℤ) * b - N * a = 1 → ∀ (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < l → ChiInv k N (N * l) χ G → (G ∣[k] toGL (wOld N l a b)) ∣[k] toGL (wOld N l a b) = ((l : ℂ) ^ (k - 2) * χ (b : ZMod N)) • G := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.wOld_slash_slash | exact GlobalTheory.HeckeFamilyMatrices.wOld_slash_slash | (intros; apply GlobalTheory.HeckeFamilyMatrices.wOld_slash_slash <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFormGammaOneOfNebentypusCuspidal
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFormGammaOneOfNebentypusCuspidal
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem cuspForm_of_chiInv : ∀ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < N →
    CuspAll k G → ChiInv k N N χ G → ∃ f : CuspForm (Gamma1 N) k, ⇑f = G := by
  intro N k χ G _ hC hχ
  refine ⟨{ toFun := G
            slash_action_eq' := fun A hA => ?_
            holo' := hC.1
            zero_at_cusps' := fun {c} hc => hC.2 c (hc.mono ?_) }, rfl⟩
  · obtain ⟨A, hA, rfl⟩ := hA
    have hA0 : A ∈ Gamma0 N := Gamma1_in_Gamma0 N hA
    have h11 : ((mat A 1 1 : ℤ) : ZMod N) = 1 := ((Gamma1_mem N A).1 hA).2.1
    have := hχ A hA0
    rw [h11, map_one, one_smul, ModularForm.SL_slash] at this
    exact this
  · rintro _ ⟨γ, -, rfl⟩; exact ⟨γ, rfl⟩
end GlobalTheory.HeckeFamilyMatrices
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFormGammaOneOfNebentypusCuspidalStatement
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspForm_gammaOne_of_nebentypus_cuspidal : ∀ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < N → CuspAll k G → ChiInv k N N χ G → ∃ f : CuspForm (Gamma1 N) k, ⇑f = G := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspForm_of_chiInv | exact GlobalTheory.HeckeFamilyMatrices.cuspForm_of_chiInv | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspForm_of_chiInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormIsCuspidalAtAllCuspsSL2
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormIsCuspidalAtAllCuspsSL2
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem cuspForm_cuspAll : ∀ (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (f : CuspForm Γ k), CuspAll k f := by
  intro Γ _ k f
  refine ⟨f.holo', fun c hc => ?_⟩
  rw [← Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (Γ : Subgroup (GL (Fin 2) ℝ))] at hc
  exact f.zero_at_cusps' hc

end GlobalTheory.HeckeFamilyMatrices
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormIsCuspidalAtAllCuspsSL2Statement
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_isCuspidalAtAllCuspsSL2 : ∀ (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (f : CuspForm Γ k), CuspAll k f := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll | exact GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OldformTraceToGammaOneEqHeckeUlLevelRaising
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OldformTraceToGammaOneEqHeckeUlLevelRaising
noncomputable section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

lemma wOld_mul_ulFam (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (j : ℕ) :
    wOld N l a b * !![1, (j : ℤ); 0, (l : ℤ)] = (l : ℤ) • mat (gaOld N l a b h j) := by
  ext i m
  fin_cases i <;> fin_cases m <;>
    simp [wOld, gaOld, mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma wOld_det (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : (wOld N l a b).det = l := by
  rw [wOld, Matrix.det_fin_two_of]; linear_combination (l : ℤ) * h

lemma mat_det_pos (γ : SL(2, ℤ)) : 0 < (mat γ).det := by simp [mat]

theorem trOld_eq : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (G : ℍ → ℂ), 0 < l →
    trOld k N l a b h G = G + ((l : ℂ) ^ (2 - k)) • UlF k l (G ∣[k] toGL (wOld N l a b)) := by
  intro N l k a b h G hl
  have hW : 0 < (wOld N l a b).det := by rw [wOld_det N l a b h]; exact_mod_cast hl
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  unfold trOld
  congr 1
  rw [UlF, hkF, Finset.smul_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← SlashAction.slash_mul, ← toGL_mul _ _ hW.ne' (ulFam_det l hl j).ne']
  have e : wOld N l a b * ulFam l j = (l : ℤ) • mat (gaOld N l a b h j) := wOld_mul_ulFam N l a b h j
  rw [e, slash_toGL_smul k l hl _ (mat_det_pos _), smul_smul, ← zpow_add₀ hl', slash_SL_eq]
  simp

end GlobalTheory.HeckeFamilyMatrices
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OldformTraceToGammaOneEqHeckeUlLevelRaisingStatement
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oldformTraceToGammaOne_eq_heckeUl_levelRaising : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (G : ℍ → ℂ), 0 < l → trOld k N l a b h G = G + ((l : ℂ) ^ (2 - k)) • UlF k l (G ∣[k] toGL (wOld N l a b)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.trOld_eq | exact GlobalTheory.HeckeFamilyMatrices.trOld_eq | (intros; apply GlobalTheory.HeckeFamilyMatrices.trOld_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlEqNebentypusOldformTraceSubDiag
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlEqNebentypusOldformTraceSubDiag
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem ulF_eq_trOld (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1)
    (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ) :
    0 < l → ChiInv k N N χ B → UlF k l B = χ (l : ZMod N) •
      (trOld k N l a b h (B ∣[k] toGL (dg l 1)) - B ∣[k] toGL (dg l 1)) := by
  intro hl hB
  let ε : SL(2, ℤ) := ⟨!![(l : ℤ), a; (N : ℤ), b], by rw [Matrix.det_fin_two_of]; linear_combination h⟩
  have hε : ε ∈ Gamma0 N := by
    rw [Gamma0_mem]; simp [ε]
  have hεB : B ∣[k] toGL (mat ε) = χ (b : ZMod N) • B := by
    rw [← slash_SL_eq, hB ε hε]; rfl
  let u : ℕ → Matrix (Fin 2) (Fin 2) ℤ := fun j => !![1, (j : ℤ); 0, (l : ℤ)]
  have hu : ∀ j, 0 < (u j).det := by
    intro j; simp [u, Matrix.det_fin_two_of]; exact_mod_cast hl
  have hD : (dg (l : ℤ) 1).det ≠ 0 := by
    simp [dg, Matrix.det_fin_two_of]; exact_mod_cast hl.ne'
  have key : ∀ j : ℕ, (B ∣[k] toGL (dg l 1)) ∣[k] gaOld N l a b h j =
      χ (b : ZMod N) • (B ∣[k] toGL (u j)) := by
    intro j
    have hg : (mat (gaOld N l a b h j)).det ≠ 0 := by simp [mat]
    have hεd : (mat ε).det ≠ 0 := by simp [mat]
    have hm : dg (l : ℤ) 1 * mat (gaOld N l a b h j) = mat ε * u j := by
      ext i i' <;> fin_cases i <;> fin_cases i' <;>
        simp [dg, gaOld, mat, ε, u, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    rw [slash_SL_eq, ← SlashAction.slash_mul, ← toGL_mul _ _ hD hg, hm, toGL_mul _ _ hεd (hu j).ne',
      SlashAction.slash_mul, hεB, smul_slash_toGL k _ (hu j)]
  have hsum : trOld k N l a b h (B ∣[k] toGL (dg l 1)) - B ∣[k] toGL (dg l 1) =
      χ (b : ZMod N) • UlF k l B := by
    rw [trOld, add_sub_cancel_left, UlF, hkF, Finset.smul_sum]
    rw [Finset.sum_congr rfl (fun j _ => key j)]
    exact (Fin.sum_univ_eq_sum_range (fun j => χ (b : ZMod N) • (B ∣[k] toGL (u j))) l).symm
  have hlb : (l : ZMod N) * (b : ZMod N) = 1 := by
    have := congrArg (fun x : ℤ => (x : ZMod N)) h
    push_cast at this
    simpa [ZMod.natCast_self] using this
  rw [hsum, smul_smul, ← map_mul, hlb, map_one, one_smul]

end GlobalTheory.HeckeFamilyMatrices
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlEqNebentypusOldformTraceSubDiagStatement
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeUl_eq_nebentypus_oldformTrace_sub_diag : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ), 0 < l → ChiInv k N N χ B → UlF k l B = χ (l : ZMod N) • (trOld k N l a b h (B ∣[k] toGL (dg l 1)) - B ∣[k] toGL (dg l 1)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.ulF_eq_trOld | exact GlobalTheory.HeckeFamilyMatrices.ulF_eq_trOld | (intros; apply GlobalTheory.HeckeFamilyMatrices.ulF_eq_trOld <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlSqSubMemOldformsGamma1
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem GlobalTheory.HeckeFamilyMatrices.ulSq_old : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Lev N l) (k : ℤ)),
  (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 (N * l) → ⇑f ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f) →
  ∃ f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ),
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₁ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₁) ∧
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₂ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₂) ∧
    UlF (k : ℤ) l (UlF (k : ℤ) l ⇑f) - (χ l * (l : ℂ) ^ (k - 2)) • ⇑f = ⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1) := by
  intro N l k hN hl hlN hk χ f hf
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  obtain ⟨u, v, huv⟩ : IsCoprime (l : ℤ) (N : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN)
  have h : (l : ℤ) * u - N * (-v) = 1 := by linear_combination huv
  haveI : NeZero N := ⟨hN0.ne'⟩
  haveI : NeZero l := ⟨hl0.ne'⟩
  haveI : (Lev N l).FiniteIndex := by unfold Lev; infer_instance
  set W := wOld N l (-v) u with hW
  set D := dg (l : ℤ) 1 with hD
  have hWdet : 0 < W.det := by
    rw [hW, wOld, Matrix.det_fin_two_of]; nlinarith
  have hDdet : 0 < D.det := by
    rw [hD, dg, Matrix.det_fin_two_of]; simpa using hl0
  set F : ℍ → ℂ := ⇑f with hFdef
  have hF : ChiInv (k : ℤ) N (N * l) χ F := hf
  have cF : CuspAll (k : ℤ) F := GlobalTheory.T.cuspForm_isCuspidalAtAllCuspsSL2 (Lev N l) k f
  set G := F ∣[(k : ℤ)] toGL W with hGdef
  have hG : ChiInv (k : ℤ) N (N * l) χ G := GlobalTheory.T.nebentypus_slash_oldformLevelRaisingMatrix N l k (-v) u h χ F hl0 hF
  have cG : CuspAll (k : ℤ) G := GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix k W F hWdet cF
  have cTr : ∀ H, CuspAll (k : ℤ) H → CuspAll (k : ℤ) (trOld k N l (-v) u h H) := by
    intro H hH
    unfold trOld
    refine cuspAll_add hH ?_
    induction (Finset.range l) using Finset.induction_on with
    | empty => simpa using cuspAll_smul 0 hH
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      refine cuspAll_add ?_ ih
      rw [slash_SL_eq]
      exact GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix k _ H (by simp [mat]) hH
  set A := trOld k N l (-v) u h F with hAdef
  set B := trOld k N l (-v) u h G with hBdef
  have hA : ChiInv (k : ℤ) N N χ A := GlobalTheory.T.nebentypus_oldformTraceToGammaOne N l k (-v) u h χ F hN0 hl hF
  have hB : ChiInv (k : ℤ) N N χ B := GlobalTheory.T.nebentypus_oldformTraceToGammaOne N l k (-v) u h χ G hN0 hl hG
  have cA : CuspAll (k : ℤ) A := cTr F cF
  have cB : CuspAll (k : ℤ) B := cTr G cG
  set C := B ∣[(k : ℤ)] toGL D with hCdef
  have hC : ChiInv (k : ℤ) N (N * l) χ C := GlobalTheory.T.nebentypus_slash_intDiagTwoMatrix_levelRaise N l k χ B hl0 hB
  have cC : CuspAll (k : ℤ) C := GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix k D B hDdet cB
  have hTC : ChiInv (k : ℤ) N N χ (trOld k N l (-v) u h C) := GlobalTheory.T.nebentypus_oldformTraceToGammaOne N l k (-v) u h χ C hN0 hl hC
  have cTC : CuspAll (k : ℤ) (trOld k N l (-v) u h C) := cTr C cC
  set c₁ : ℂ := χ (l : ZMod N) with hc₁
  set p : ℂ := (l : ℂ) ^ ((k : ℤ) - 2) with hp
  have h₁ : ChiInv (k : ℤ) N N χ (c₁ ^ 2 • trOld k N l (-v) u h C + (-(c₁ * p)) • A) :=
    chiInv_add (chiInv_smul _ hTC) (chiInv_smul _ hA)
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.T.exists_cuspForm_gammaOne_of_nebentypus_cuspidal N k χ (c₁ ^ 2 • trOld k N l (-v) u h C + (-(c₁ * p)) • A) hN0
    (cuspAll_add (cuspAll_smul _ cTC) (cuspAll_smul _ cA)) h₁
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.T.exists_cuspForm_gammaOne_of_nebentypus_cuspidal N k χ (-(c₁ ^ 2) • B) hN0 (cuspAll_smul _ cB) (chiInv_smul _ hB)
  refine ⟨f₁, f₂, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩
  · rw [hf₁]; exact h₁ γ hγ
  · rw [hf₂]; exact chiInv_smul _ hB γ hγ
  rw [hf₁, hf₂]
  have e1 := GlobalTheory.T.oldformTraceToGammaOne_eq_heckeUl_levelRaising N l k (-v) u h F hl0
  have e2 := GlobalTheory.T.oldformTraceToGammaOne_eq_heckeUl_levelRaising N l k (-v) u h G hl0
  have e3 := GlobalTheory.T.oldformLevelRaising_slash_slash_nebentypus N l k (-v) u h χ F hl0 hF
  have e4 := GlobalTheory.T.heckeUl_eq_nebentypus_oldformTrace_sub_diag N l k (-v) u h χ B hl0 hB
  rw [← hAdef, ← hGdef] at e1
  rw [← hBdef, e3] at e2
  rw [← hCdef] at e4
  have cb : c₁ * χ (u : ZMod N) = 1 := by
    rw [hc₁, ← map_mul]
    have h2 := congrArg (Int.cast : ℤ → ZMod N) h
    push_cast at h2
    rw [ZMod.natCast_self] at h2
    rw [show ((l : ZMod N) * (u : ZMod N)) = 1 by linear_combination h2, map_one]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
  have pp : p * (l : ℂ) ^ (2 - (k : ℤ)) = 1 := by
    rw [hp, ← zpow_add₀ hl']; simp
  have hUG : UlF k l G = p • (A - F) := by
    rw [e1, add_sub_cancel_left, smul_smul, pp, one_smul]
  have hUF : UlF k l F = c₁ • (B - G) := by
    have key : c₁ * (l : ℂ) ^ (2 - (k : ℤ)) * ((l : ℂ) ^ ((k : ℤ) - 2) * χ (u : ZMod N)) = 1 := by
      rw [← hp]
      calc c₁ * (l : ℂ) ^ (2 - (k : ℤ)) * (p * χ (u : ZMod N))
          = (p * (l : ℂ) ^ (2 - (k : ℤ))) * (c₁ * χ (u : ZMod N)) := by ring
        _ = 1 := by rw [pp, cb, one_mul]
    rw [e2, add_sub_cancel_left, ulF_smul k l hl0, smul_smul, smul_smul, key, one_smul]
  have hpk : (l : ℂ) ^ (k - 2) = p := by
    rw [hp, show ((k : ℤ) - 2) = ((k - 2 : ℕ) : ℤ) by omega, zpow_natCast]
  rw [hpk, hUF, ulF_smul k l hl0, ulF_sub k l hl0, e4, hUG, smul_slash_toGL k D hDdet, ← hCdef]
  funext τ
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlSqSubMemOldformsGamma1Statement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_Ul_sq_sub_mem_oldforms_Gamma1 : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Lev N l) (k : ℤ)),
  (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 (N * l) → ⇑f ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f) →
  ∃ f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ),
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₁ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₁) ∧
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₂ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₂) ∧
    UlF (k : ℤ) l (UlF (k : ℤ) l ⇑f) - (χ l * (l : ℂ) ^ (k - 2)) • ⇑f = ⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.ulSq_old | exact GlobalTheory.HeckeFamilyMatrices.ulSq_old | (intros; apply GlobalTheory.HeckeFamilyMatrices.ulSq_old <;> assumption)
end
end

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.UlSemisimple

theorem toGL_det (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    (toGL g : Matrix (Fin 2) (Fin 2) ℝ).det = (g.det : ℝ) := by
  unfold toGL
  rw [dite_eq_right hg]
  simp only [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two]
  simp [Matrix.det_fin_two]

theorem slash_smul_pos (k : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : 0 < g.det) (c : ℂ) (f : ℍ → ℂ) :
    (c • f) ∣[k] toGL g = c • (f ∣[k] toGL g) := by
  rw [ModularForm.smul_slash]
  congr 1
  simp only [UpperHalfPlane.σ]
  rw [if_pos (by rw [Matrix.GeneralLinearGroup.val_det_apply, toGL_det g hg.ne']; exact_mod_cast hg)]
  rfl

def ulLin (k : ℤ) (l : ℕ) (hl : 0 < l) : Module.End ℂ (ℍ → ℂ) where
  toFun := UlF k l
  map_add' f g := by simp only [UlF, hkF, SlashAction.add_slash, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [UlF, hkF, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => slash_smul_pos k _ ?_ c f
    simp [ulFam, Matrix.det_fin_two]
    exact_mod_cast hl

theorem ulLin_apply (k : ℤ) (l : ℕ) (hl : 0 < l) (F : ℍ → ℂ) : ulLin k l hl F = UlF k l F := rfl

def ChiLaw (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (F : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → F ∣[k] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • F

def oldSp (N l : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (hl : 0 < l) : Submodule ℂ (ℍ → ℂ) where
  carrier := {F | ∃ f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma1 N) k, ChiLaw N k χ ⇑f₁ ∧ ChiLaw N k χ ⇑f₂ ∧
    F = ⇑f₁ + ⇑f₂ ∣[k] toGL (dg l 1)}
  add_mem' := by
    rintro F G ⟨f₁, f₂, h₁, h₂, rfl⟩ ⟨g₁, g₂, h₁', h₂', rfl⟩
    refine ⟨f₁ + g₁, f₂ + g₂, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩
    · rw [CuspForm.coe_add, SlashAction.add_slash, h₁ γ hγ, h₁' γ hγ, smul_add]
    · rw [CuspForm.coe_add, SlashAction.add_slash, h₂ γ hγ, h₂' γ hγ, smul_add]
    · rw [CuspForm.coe_add, CuspForm.coe_add, SlashAction.add_slash]; abel
  zero_mem' := ⟨0, 0, fun γ _ => by simp, fun γ _ => by simp, by simp⟩
  smul_mem' := by
    rintro c F ⟨f₁, f₂, h₁, h₂, rfl⟩
    have hd : 0 < (dg (l : ℤ) 1).det := by simp [dg, Matrix.det_fin_two]; exact_mod_cast hl
    refine ⟨c • f₁, c • f₂, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩
    · rw [CuspForm.coe_smul, ModularForm.SL_smul_slash, h₁ γ hγ, smul_comm]
    · rw [CuspForm.coe_smul, ModularForm.SL_smul_slash, h₂ γ hγ, smul_comm]
    · rw [CuspForm.coe_smul, CuspForm.coe_smul, slash_smul_pos k _ hd, smul_add]

theorem aeval_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (U : Module.End ℂ M) (O : Submodule ℂ M)
    (hU : ∀ x ∈ O, U x ∈ O) (p : ℂ[X]) (x : M) (hx : x ∈ O) : aeval U p x ∈ O := by
  have hpow : ∀ m : ℕ, ∀ y ∈ O, (U ^ m) y ∈ O := by
    intro m
    induction m with
    | zero => intro y hy; simpa using hy
    | succ m ih => intro y hy; rw [pow_succ', Module.End.mul_apply]; exact hU _ (ih y hy)
  rw [aeval_eq_sum_range, LinearMap.sum_apply]
  exact O.sum_mem fun i _ => by rw [LinearMap.smul_apply]; exact O.smul_mem _ (hpow i x hx)

end GlobalTheory.HeckeFamilyMatrices.UlSemisimple


open GlobalTheory.HeckeFamilyMatrices.UlSemisimple in
theorem GlobalTheory.HeckeFamilyMatrices.ul_semisimple : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (α : ℂ), α ^ 2 ≠ χ l * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ χ l * (l : ℂ) ^ (k - 2) →
  ∀ f : CuspForm (Lev N l) (k : ℤ), (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 (N * l) → ⇑f ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f) →
  ∀ n : ℕ, (fun F => UlF (k : ℤ) l F - α • F)^[n] ⇑f = 0 → UlF (k : ℤ) l ⇑f = α • ⇑f := by
  intro N l k hN hl hlN hk χ α hα1 hα2 f hf n hn
  have hl0 : 0 < l := hl.pos
  set U := ulLin (k : ℤ) l hl0 with hUdef
  set O := oldSp N l (k : ℤ) χ hl0 with hOdef
  have hUO : ∀ F ∈ O, U F ∈ O := by
    rintro F ⟨f₁, f₂, h₁, h₂, rfl⟩
    obtain ⟨g₁, g₂, hg₁, hg₂, he⟩ := (GlobalTheory.T.heckeUl_semisimple_on_lOldSpace N l k hN hl hlN hk χ α hα1 f₁ f₂ h₁ h₂).1
    exact ⟨g₁, g₂, hg₁, hg₂, he⟩
  set c : ℂ := χ l * (l : ℂ) ^ (k - 2) with hc
  have hcop : IsCoprime ((X - C α) ^ n) (X ^ 2 - C c) := by
    apply IsCoprime.pow_left
    rw [(irreducible_X_sub_C α).coprime_iff_not_dvd, dvd_iff_isRoot, IsRoot.def]
    simpa [sub_eq_zero] using hα2
  obtain ⟨A, B, hAB⟩ := hcop
  have key : aeval U A (aeval U ((X - C α) ^ n) ⇑f) + aeval U B (aeval U (X ^ 2 - C c) ⇑f) = ⇑f := by
    have := congrArg (fun p => aeval U p ⇑f) hAB
    simpa only [map_add (f := _), map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.one_apply] using this
  have h1 : aeval U ((X - C α) ^ n) ⇑f = 0 := by
    rw [map_pow, map_sub, aeval_X, aeval_C, Module.End.pow_apply]
    convert hn using 2
    funext F
    simp [hUdef, ulLin_apply, Module.algebraMap_end_apply]
  have h2 : aeval U (X ^ 2 - C c) ⇑f ∈ O := by
    obtain ⟨f₁, f₂, h₁, h₂, he⟩ := GlobalTheory.T.hecke_Ul_sq_sub_mem_oldforms_Gamma1 N l k hN hl hlN hk χ f hf
    refine ⟨f₁, f₂, h₁, h₂, ?_⟩
    rw [← he, map_sub, aeval_C, map_pow, aeval_X, LinearMap.sub_apply, Module.algebraMap_end_apply,
      pow_two, Module.End.mul_apply]
    rfl
  have hfO : ⇑f ∈ O := by
    rw [← key, h1, map_zero, zero_add]
    exact aeval_mem U O hUO B _ h2
  obtain ⟨f₁, f₂, h₁, h₂, he⟩ := hfO
  have hss := (GlobalTheory.T.heckeUl_semisimple_on_lOldSpace N l k hN hl hlN hk χ α hα1 f₁ f₂ h₁ h₂).2 n
  rw [he] at hn ⊢
  exact hss hn

end
