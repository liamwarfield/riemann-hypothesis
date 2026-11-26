module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsWignerContractionChainLowering
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsWignerContractionChainRaising
public import Development.AbelianVarietyTheory.Definitions.Jets.FactorNonneg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExistsAndVectorEqSmulTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUnitaryWFrameToFrame
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P

namespace GlobalTheory.FrameTrans

variable {k r : ℕ}

noncomputable def swapMat (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (B B' : Fin k → Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  1 + Matrix.of fun p q => ∑ c, (B' c p - B c p) * herm H (bvec q) (B c)

end GlobalTheory.FrameTrans

namespace GlobalTheory

end GlobalTheory
end

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory

open Formalism.FourierDecayAlt.P

private theorem Hpk_mulVec_of_inWb {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : _root_.Formalism.QuantumDeterminants.inWb k r v) :
    _root_.Formalism.QuantumDeterminants.Hpk k r *ᵥ v = fun i : Fin (2 * r + k + 1) => if (i : ℕ) = r + k then -v i else v i := by
  funext i
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases hi : (i : ℕ) < r ∨ r + k < i
    · rw [hv i hi]; simp
    · push_neg at hi
      have h1 : ¬ (i : ℕ) < r := by omega
      simp only [_root_.Formalism.QuantumDeterminants.Hpk, h1, false_and, if_false, hi.1, hi.2, true_and, if_true]
      split_ifs <;> simp
  · intro j _ hj
    by_cases hjm : (j : ℕ) < r ∨ r + k < j
    · rw [hv j hjm]; simp
    · push_neg at hjm
      have hne : (i : ℕ) ≠ j := fun h => hj (Fin.ext h).symm
      simp only [_root_.Formalism.QuantumDeterminants.Hpk]
      split_ifs with h1 h2 h3 <;> first | omega | exact absurd (congrArg Fin.val h3.2.2) hne | simp
  · simp

private theorem herm_smul_left_jet_harmonics {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (c : ℂ) (v w : ι → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm H (c • v) w = c * _root_.Formalism.QuantumDeterminants.herm H v w := by
  simp [_root_.Formalism.QuantumDeterminants.herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem herm_smul_right_jet_harmonics {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) (c : ℂ) (v w : ι → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm H v (c • w) = star c * _root_.Formalism.QuantumDeterminants.herm H v w := by
  simp [_root_.Formalism.QuantumDeterminants.herm, star_smul, smul_dotProduct, smul_eq_mul]

private theorem exists_unit_orth_in_Wb {n r : ℕ} {z : Fin (2 * r + (n + 1) + 1) → ℂ} (hz : _root_.Formalism.QuantumDeterminants.inWb (n + 1) r z)
    (hT : 0 < _root_.Formalism.QuantumDeterminants.Tz (n + 1) r z) :
    ∃ e, _root_.Formalism.QuantumDeterminants.inWb (n + 1) r e ∧ _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) e z = 0 ∧
      _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) e e = 1 := by
  set p : Fin (2 * r + (n + 1) + 1) := ⟨r, by omega⟩ with hp
  set q : Fin (2 * r + (n + 1) + 1) := ⟨r + (n + 1), by omega⟩ with hq
  have hpq : p ≠ q := by simp [hp, hq, Fin.ext_iff]
  set v : Fin (2 * r + (n + 1) + 1) → ℂ := Pi.single p (star (z q)) + Pi.single q (star (z p)) with hvdef
  have hv : _root_.Formalism.QuantumDeterminants.inWb (n + 1) r v := by
    intro i hi
    have hip : i ≠ p := fun h => by rw [h] at hi; simp [hp] at hi
    have hiq : i ≠ q := fun h => by rw [h] at hi; simp [hq] at hi
    simp [hvdef, Pi.single_apply, hip, hiq]
  have hpval : (p : ℕ) ≠ r + (n + 1) := by simp [hp]
  have hqval : (q : ℕ) = r + (n + 1) := by simp [hq]
  have hHv : _root_.Formalism.QuantumDeterminants.Hpk (n + 1) r *ᵥ v = Pi.single p (star (z q)) - Pi.single q (star (z p)) := by
    rw [Hpk_mulVec_of_inWb hv]
    funext i
    by_cases hip : i = p
    · rw [hip, if_neg hpval, hvdef]
      simp [hpq, hpq.symm]
    · by_cases hiq : i = q
      · rw [hiq, if_pos hqval, hvdef]
        simp [hpq, hpq.symm]
      · have : (i : ℕ) ≠ r + (n + 1) := fun h => hiq (Fin.ext (h.trans hqval.symm))
        rw [if_neg this, hvdef]
        simp [hip, hiq]
  have hvz : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) v z = 0 := by
    rw [_root_.Formalism.QuantumDeterminants.herm, hHv, dotProduct_sub, dotProduct_single, dotProduct_single]
    simp [mul_comm]
  have hvv : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) v v =
      ((Complex.normSq (z q) - Complex.normSq (z p) : ℝ) : ℂ) := by
    rw [_root_.Formalism.QuantumDeterminants.herm, hHv, dotProduct_sub, dotProduct_single, dotProduct_single]
    simp [hvdef, hpq, hpq.symm, Complex.normSq_eq_conj_mul_self]
    ring
  have hzz : Complex.normSq (z p) - Complex.normSq (z q) ≤ (_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) z z).re := by
    rw [_root_.Formalism.QuantumDeterminants.herm, Hpk_mulVec_of_inWb hz]
    simp only [dotProduct, Complex.re_sum]
    have hf : ∀ i : Fin (2 * r + (n + 1) + 1),
        (star (z i) * (if (i : ℕ) = r + (n + 1) then -z i else z i)).re =
          if (i : ℕ) = r + (n + 1) then -Complex.normSq (z i) else Complex.normSq (z i) := by
      intro i
      split_ifs <;> simp [Complex.normSq_apply, Complex.mul_re] <;> ring
    simp only [Pi.star_apply, hf]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q), if_pos hqval]
    have hpe : p ∈ Finset.univ.erase q := Finset.mem_erase.2 ⟨hpq, Finset.mem_univ _⟩
    have h2 := Finset.single_le_sum (f := fun i : Fin (2 * r + (n + 1) + 1) =>
        if (i : ℕ) = r + (n + 1) then -Complex.normSq (z i) else Complex.normSq (z i))
      (fun i hi => by
        have hiq : (i : ℕ) ≠ r + (n + 1) := fun h =>
          Finset.ne_of_mem_erase hi (Fin.ext (h.trans hqval.symm))
        simp only [if_neg hiq]
        exact Complex.normSq_nonneg _) hpe
    simp only [if_neg hpval] at h2
    linarith
  have hT' : (_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) z z).re < 0 := by
    have := hT; unfold _root_.Formalism.QuantumDeterminants.Tz at this; linarith
  set t := Complex.normSq (z q) - Complex.normSq (z p) with htdef
  have ht : 0 < t := by linarith
  refine ⟨((Real.sqrt t : ℂ))⁻¹ • v, fun i hi => by simp [hv i hi], ?_, ?_⟩
  · rw [herm_smul_left_jet_harmonics, hvz, mul_zero]
  · rw [herm_smul_left_jet_harmonics, herm_smul_right_jet_harmonics, hvv]
    have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
    have hs0 : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 ht).ne'
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
    exact_mod_cast hs.symm

private theorem swapMat_eq_one_add_sub_mul {k r : ℕ} (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (B B' : Fin k → Fin (2 * r + k + 1) → ℂ) :
    _root_.GlobalTheory.FrameTrans.swapMat H B B' = 1 + (_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B' - _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B) * ((_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B)ᴴ * H) := by
  ext p q
  simp [_root_.GlobalTheory.FrameTrans.swapMat, Matrix.mul_apply, _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM, _root_.Formalism.QuantumDeterminants.herm, _root_.Formalism.QuantumDeterminants.bvec, dotProduct, mulVec, Pi.single_apply, Finset.mul_sum]

private theorem swapMat_mulVec' {k r : ℕ} (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (B B' : Fin k → Fin (2 * r + k + 1) → ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    _root_.GlobalTheory.FrameTrans.swapMat H B B' *ᵥ v =
      v + (_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B' - _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B) *ᵥ fun c => _root_.Formalism.QuantumDeterminants.herm H v (B c) := by
  rw [swapMat_eq_one_add_sub_mul, add_mulVec, one_mulVec, ← mulVec_mulVec]
  congr 2
  funext c
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
    _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM, Matrix.of_apply,
    _root_.Formalism.QuantumDeterminants.herm, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

private theorem colM_eq_mul_gram_of_isFrameOf {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : _root_.Formalism.QuantumDeterminants.inWb k r z)
    (hzz : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) z z ≠ 0) {B B' : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] B) (hB' : _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] B') :
    _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B' = _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B * ((_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B') := by
  ext p c
  have e := congrFun (_root_.Formalism.FourierDecayAlt.P.HermitianFormSums.complete0 hz hzz hB (hB'.1 c) (hB'.2.2 c z (List.mem_singleton_self z))) p
  rw [Matrix.mul_apply]
  simp only [_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.gramM_apply]
  simp only [_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM, Matrix.of_apply]
  conv_lhs => rw [e]
  simp [Finset.sum_apply, mul_comm]

private theorem swapMat_mem_UWset_of_isFrameOf {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : _root_.Formalism.QuantumDeterminants.inWb k r z)
    (hzz : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) z z ≠ 0) {B B' : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] B) (hB' : _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] B') :
    _root_.GlobalTheory.FrameTrans.swapMat (_root_.Formalism.QuantumDeterminants.Hpk k r) B B' ∈ _root_.Formalism.QuantumDeterminants.UWset k r z := by
  have hfix : ∀ j, _root_.GlobalTheory.FrameTrans.swapMat (_root_.Formalism.QuantumDeterminants.Hpk k r) B B' *ᵥ _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.cvec k r z j = _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.cvec k r z j := by
    intro j
    rw [swapMat_mulVec']
    have h0 : (fun c => _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.cvec k r z j) (B c)) = 0 := funext fun c => _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.gram_VC hB c j
    rw [h0, mulVec_zero, add_zero]
  refine ⟨?_, fun a => ⟨hfix (Sum.inl a), hfix (Sum.inr (Sum.inl a))⟩, hfix (Sum.inr (Sum.inr ()))⟩
  set H := _root_.Formalism.QuantumDeterminants.Hpk k r with hHdef
  set V := _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B with hVdef
  set V' := _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B' with hV'def
  have hH : Hᴴ = H := _root_.Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  have gram : ∀ {C : Fin k → Fin (2 * r + k + 1) → ℂ}, _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] C → (_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM C)ᴴ * H * _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM C = 1 := by
    intro C hC
    ext i j
    rw [_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.gramM_apply, hC.2.1 j i, Matrix.one_apply]
    simp [eq_comm]
  have hgramV : Vᴴ * H * V = 1 := gram hB
  have hgramV' : V'ᴴ * H * V' = 1 := gram hB'
  set M := Vᴴ * H * V' with hMdef
  have hM : V' = V * M := colM_eq_mul_gram_of_isFrameOf hz hzz hB hB'
  have hMM : Mᴴ * M = 1 := by
    calc Mᴴ * M = Mᴴ * (Vᴴ * H * V) * M := by rw [hgramV, Matrix.mul_one]
      _ = (V * M)ᴴ * H * (V * M) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [← hM, hgramV']
  have hG : ∀ X : Matrix (Fin k) (Fin (2 * r + k + 1)) ℂ, Vᴴ * (H * (V * X)) = X := by
    intro X; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hgramV, Matrix.one_mul]
  have hQ : (M - 1) + (Mᴴ - 1) + (Mᴴ - 1) * (M - 1) = 0 := by
    simp only [sub_mul, mul_sub, hMM, Matrix.mul_one, Matrix.one_mul]; abel
  show _ * H * _ = H
  rw [swapMat_eq_one_add_sub_mul]
  have hVV : V' - V = V * (M - 1) := by rw [Matrix.mul_sub, Matrix.mul_one, ← hM]
  rw [hVV]
  calc (1 + V * (M - 1) * (Vᴴ * H))ᴴ * H * (1 + V * (M - 1) * (Vᴴ * H))
      = H + H * (V * (((M - 1) + (Mᴴ - 1) + (Mᴴ - 1) * (M - 1)) * (Vᴴ * H))) := by
        simp only [conjTranspose_add, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose, hH,
          conjTranspose_sub, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hG]
        abel
    _ = H := by rw [hQ]; simp

theorem _root_.GlobalTheory.frame_exists_and_vector_eq_smul_translate :
    ∀ (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)), _root_.Formalism.QuantumDeterminants.inWb (n + 1) r z → 0 < _root_.Formalism.QuantumDeterminants.Tz (n + 1) r z →
      (∃ B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ), _root_.Formalism.FourierDecayAlt.Q.IsFrameOf (n + 1) r [z] B) ∧
      ∀ B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ), _root_.Formalism.FourierDecayAlt.Q.IsFrameOf (n + 1) r [z] B →
        ∀ w, _root_.Formalism.QuantumDeterminants.inWb (n + 1) r w → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) w z = 0 →
          ∃ (t : ℝ), ∃ h ∈ _root_.Formalism.QuantumDeterminants.UWset (n + 1) r z, 0 ≤ t ∧ (_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) w w).re = t ^ 2 ∧
            w = (t : ℂ) • (h *ᵥ B (Fin.last n)) := by
  intro n r z hz hT
  have hzz := _root_.Formalism.FourierDecayAlt.P.HermitianFormSums.hzz hT
  have key : ∀ e, _root_.Formalism.QuantumDeterminants.inWb (n + 1) r e → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) e z = 0 →
      _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) e e = 1 →
        ∃ B' : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ),
          _root_.Formalism.FourierDecayAlt.Q.IsFrameOf (n + 1) r [z] B' ∧ B' (Fin.last n) = e := by
    intro e he hez hee
    obtain ⟨Bs, hBs⟩ := _root_.Formalism.FourierDecayAlt.P.exists_frame_two n r z e hz hT he hez hee
    exact ⟨Fin.snoc Bs e, _root_.Formalism.FourierDecayAlt.P.FrameExtension.frame_snoc hBs he hez hee, by simp⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨e, he, hez, hee⟩ := exists_unit_orth_in_Wb hz hT
    obtain ⟨B', hB', -⟩ := key e he hez hee
    exact ⟨B', hB'⟩
  intro B hB w hw hwz
  have hexp := _root_.Formalism.FourierDecayAlt.P.HermitianFormSums.complete0 hz hzz hB hw hwz
  set S := ∑ a, Complex.normSq (_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) w (B a)) with hS
  have hww : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) w w = (S : ℂ) := by
    conv_lhs => rw [hexp]
    rw [_root_.Formalism.FourierDecayAlt.P.HermitianFormSums.herm_comb hB, hS]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Complex.mul_conj _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _
  have hre : (_root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) w w).re = S := by rw [hww, Complex.ofReal_re]
  have hone : _root_.GlobalTheory.FrameTrans.swapMat (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) B B ∈ _root_.Formalism.QuantumDeterminants.UWset (n + 1) r z :=
    swapMat_mem_UWset_of_isFrameOf hz hzz hB hB
  by_cases hw0 : w = 0
  · refine ⟨0, 1, ?_, le_rfl, ?_, ?_⟩
    · rwa [swapMat_eq_one_add_sub_mul, sub_self, Matrix.zero_mul, add_zero] at hone
    · rw [hre]
      subst hw0
      simp [hS, _root_.Formalism.QuantumDeterminants.herm]
    · simp [hw0]
  have hSpos : 0 < S := by
    refine lt_of_le_of_ne hS0 fun h0 => hw0 ?_
    rw [hexp]
    refine Finset.sum_eq_zero fun a _ => ?_
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).1 h0.symm a
      (Finset.mem_univ _)
    rw [Complex.normSq_eq_zero.1 this, zero_smul]
  set t := Real.sqrt S with htdef
  have ht0 : 0 < t := Real.sqrt_pos.2 hSpos
  have htS : t ^ 2 = S := Real.sq_sqrt hS0
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have he : _root_.Formalism.QuantumDeterminants.inWb (n + 1) r ((t : ℂ)⁻¹ • w) := fun i hi => by simp [hw i hi]
  have hez : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) ((t : ℂ)⁻¹ • w) z = 0 := by
    rw [herm_smul_left_jet_harmonics, hwz, mul_zero]
  have hee : _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) ((t : ℂ)⁻¹ • w) ((t : ℂ)⁻¹ • w) = 1 := by
    rw [herm_smul_left_jet_harmonics, herm_smul_right_jet_harmonics, hww, ← htS]
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    push_cast
    field_simp
  obtain ⟨B', hB', hlast⟩ := key _ he hez hee
  refine ⟨t, _root_.GlobalTheory.FrameTrans.swapMat (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) B B', swapMat_mem_UWset_of_isFrameOf hz hzz hB hB', ht0.le,
    by rw [hre, htS], ?_⟩
  have hsingle : (fun c => _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk (n + 1) r) (B (Fin.last n)) (B c)) = Pi.single (Fin.last n) 1 := by
    funext c
    rw [hB.2.1]
    simp [Pi.single_apply, eq_comm]
  rw [swapMat_mulVec', hsingle, Matrix.mulVec_single_one]
  have hcol : (_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B' - _root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM B).col (Fin.last n) = B' (Fin.last n) - B (Fin.last n) := by
    funext p
    simp [_root_.Formalism.FourierDecayAlt.P.HermitianFormRankFour.colM]
  rw [hcol, add_sub_cancel, hlast, smul_smul, mul_inv_cancel₀ htc, one_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormAdjointApplyOfNormPreserving
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem norm_adjoint_apply_of_norm_preserving {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (P : V →L[ℂ] V) (hP : ∀ v, ‖P v‖ = ‖v‖) (v : V) :
    ‖ContinuousLinearMap.adjoint P v‖ = ‖v‖ := by
  let L : V →ₗᵢ[ℂ] V := ⟨(P : V →ₗ[ℂ] V), hP⟩
  have hsurj : Function.Surjective (P : V →ₗ[ℂ] V) :=
    LinearMap.surjective_of_injective (f := (P : V →ₗ[ℂ] V)) L.injective
  obtain ⟨u, rfl⟩ := hsurj v
  have h1 : ContinuousLinearMap.adjoint P (P u) = u := by
    apply ext_inner_right ℂ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact L.inner_map_map u w
  change ‖ContinuousLinearMap.adjoint P (P u)‖ = ‖P u‖
  rw [h1, hP]

theorem norm_adjoint_of_intertwine {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (P : V →L[ℂ] V) (Q : U →L[ℂ] U) (A A' : U →L[ℂ] V) (hQ : ∀ v, ‖Q v‖ = ‖v‖)
    (h : A'.comp Q = P.comp A) (v : V) :
    ‖ContinuousLinearMap.adjoint A' v‖ = ‖ContinuousLinearMap.adjoint A (ContinuousLinearMap.adjoint P v)‖ := by
  rw [← norm_adjoint_apply_of_norm_preserving Q hQ]
  have h1 := congrArg (fun T : U →L[ℂ] V => ContinuousLinearMap.adjoint T v) h
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply] at h1
  rw [h1]

theorem norm_adjoint_real_pow_smul {V U : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    (A : U →L[ℂ] V) (t : ℝ) (d : ℕ) (v : V) :
    ‖ContinuousLinearMap.adjoint (((t : ℂ) ^ d) • A) v‖ ^ 2 =
      (t ^ 2) ^ d * ‖ContinuousLinearMap.adjoint A v‖ ^ 2 := by
  rw [LinearIsometryEquiv.map_smulₛₗ, ContinuousLinearMap.smul_apply, norm_smul, mul_pow]
  congr 1
  rw [RCLike.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← pow_mul, mul_comm, pow_mul, sq_abs]

theorem lower_bound_spreads :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (πp : Mx (n + 1) r → (Vp →L[ℂ] Vp)) (πm : Mx (n + 1) r → (Vm →L[ℂ] Vm)) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (Ap : (Fin (2 * r + (n + 1) + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + (n + 1) + 1) → ℂ) → (Vm →L[ℂ] V)) (n₀ : ℕ) (b : ℝ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖π h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖πp h v‖ = ‖v‖) → (∀ h ∈ UWset (n + 1) r z, ∀ v, ‖πm h v‖ = ‖v‖) → IsFrameOf (n + 1) r [z] B → GlobalTheory.WigSh.WigMap (n + 1) r z πp π n₀ Ap → GlobalTheory.WigSh.WigMap (n + 1) r z πm π n₀ Am → (∀ v : V, ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap (B (Fin.last n))) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am (B (Fin.last n))) v‖ ^ 2)) → ∀ ω, inWb (n + 1) r ω → herm (Hpk (n + 1) r) ω z = 0 → ∀ v : V, (herm (Hpk (n + 1) r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  intro V _ _ _ Vp _ _ _ Vm _ _ _ n r z π πp πm B Ap Am n₀ b hz hT hπ hπp hπm hB hAp hAm hlow ω hω hωz v
  obtain ⟨t, h, hh, -, hre, rfl⟩ :=
    (GlobalTheory.frame_exists_and_vector_eq_smul_translate n r z hz hT).2 B hB ω hω hωz
  rw [hre, hAp.2.2.1, hAm.2.2.1, norm_adjoint_real_pow_smul, norm_adjoint_real_pow_smul,
    norm_adjoint_of_intertwine (π h) (πp h) _ _ (hπp h hh) (hAp.2.1 h hh _),
    norm_adjoint_of_intertwine (π h) (πm h) _ _ (hπm h hh) (hAm.2.1 h hh _)]
  have h1 := hlow (ContinuousLinearMap.adjoint (π h) v)
  rw [norm_adjoint_apply_of_norm_preserving (π h) (hπ h hh)] at h1
  have h2 : (0 : ℝ) ≤ (t ^ 2) ^ n₀ := by positivity
  calc _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
    _ = _ := by ring

end GlobalTheory.WigSh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChainLowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvSqLeWignerCoeffSqRaising
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvSqLeWignerCoeffSqRaising
open Finset

noncomputable section

namespace GlobalTheory.WigSh

theorem prod_other_neighbour_raise {n : ℕ} (d : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (hd : ∀ i, 0 < d i) (hl : d l = 1) :
    (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc)) * (d 0 * d (Fin.last n))
      = ∏ j : Fin n, d (l.succAbove j) := by
  have hP : ∏ i, d i = ∏ j : Fin n, d (l.succAbove j) := by
    rw [Fin.prod_univ_succAbove d l, hl, one_mul]
  have h1 := Fin.prod_univ_succ d
  have h2 := Fin.prod_univ_castSucc d
  have h3 : (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
      * ∏ j : Fin n, d (l.succAbove j) = (∏ j : Fin n, d j.succ) * ∏ j : Fin n, d j.castSucc := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold Fin.succAbove
    split_ifs
    · rfl
    · exact mul_comm _ _
  have hpos : 0 < ∏ j : Fin n, d (l.succAbove j) := Finset.prod_pos fun j _ => hd _
  apply mul_right_cancel₀ hpos.ne'
  calc _ = ((∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
      * ∏ j : Fin n, d (l.succAbove j)) * (d 0 * d (Fin.last n)) := by ring
    _ = (d 0 * ∏ j : Fin n, d j.succ) * ((∏ j : Fin n, d j.castSucc) * d (Fin.last n)) := by
      rw [h3]; ring
    _ = _ := by rw [← h1, ← h2, hP]

theorem inv_sq_le_wP (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ)
    (hL : StrictAnti L) (hM : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc)
    (hne : ∀ j, M j ≠ L l + 1) (hD : 1 ≤ D) (h0 : (L 0 : ℝ) - L l ≤ D)
    (hn : (L l : ℝ) - L (Fin.last n) ≤ D) : (D ^ 2)⁻¹ ≤ wP L M l := by
  set e : Fin (n + 1) → ℤ := fun i => max |L i - L l| 1 with he
  set d : Fin (n + 1) → ℝ := fun i => (e i : ℝ) with hd
  have hdpos : ∀ i, 0 < d i := fun i => by
    have : 0 < e i := lt_of_lt_of_le one_pos (le_max_right _ _)
    simp only [hd]; exact_mod_cast this
  have hdl : d l = 1 := by simp [hd, he]
  have key := prod_other_neighbour_raise d l hdpos hdl
  have hd0 : d 0 ≤ D := by
    have a : L l ≤ L 0 := hL.antitone (Fin.zero_le _)
    have a' : (L l : ℝ) ≤ L 0 := by exact_mod_cast a
    simp only [hd, he]
    push_cast
    exact max_le (by rw [abs_of_nonneg (by linarith)]; exact h0) hD
  have hdn : d (Fin.last n) ≤ D := by
    have a : L (Fin.last n) ≤ L l := hL.antitone (Fin.le_last _)
    have a' : (L (Fin.last n) : ℝ) ≤ L l := by exact_mod_cast a
    simp only [hd, he]
    push_cast
    exact max_le (by rw [abs_of_nonpos (by linarith)]; linarith) hD
  have hden : ∏ j : Fin n, |(L (l.succAbove j) : ℝ) - L l| = ∏ j : Fin n, d (l.succAbove j) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    have a : L (l.succAbove j) ≠ L l := fun h => Fin.succAbove_ne l j (hL.injective h)
    have b : 1 ≤ |L (l.succAbove j) - L l| := Int.one_le_abs (sub_ne_zero.2 a)
    simp only [hd, he, max_eq_left b]
    push_cast
    rfl
  have hnum : (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
      ≤ ∏ j : Fin n, |(M j : ℝ) - 1 - L l| := by
    refine Finset.prod_le_prod₀ (fun j _ => (hdpos _).le) fun j _ => ?_
    obtain ⟨h1, h2⟩ := hM j
    have h3 := hne j
    have : e (if j.castSucc < l then j.succ else j.castSucc) ≤ |M j - 1 - L l| := by
      split_ifs with hl
      · have a2 : L l ≤ L j.succ := hL.antitone (Fin.castSucc_lt_iff_succ_le.1 hl)
        simp only [he]
        rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
        omega
      · have a2 : L j.castSucc ≤ L l := hL.antitone (not_lt.1 hl)
        simp only [he]
        rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]
        omega
    simp only [hd]
    exact_mod_cast this
  rw [← abs_of_nonneg (Model.placeWeight_nonneg hM l)]
  unfold wP
  rw [Model.prod_erase_eq, abs_div, Finset.abs_prod, Finset.abs_prod, hden, ← key]
  have hQ : 0 < ∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc) :=
    Finset.prod_pos fun j _ => hdpos _
  have hm : d 0 * d (Fin.last n) ≤ D ^ 2 := by
    rw [sq]; exact mul_le_mul hd0 hdn (hdpos _).le (by linarith)
  have hmpos : 0 < d 0 * d (Fin.last n) := mul_pos (hdpos _) (hdpos _)
  calc (D ^ 2)⁻¹ ≤ (d 0 * d (Fin.last n))⁻¹ := inv_anti₀ hmpos hm
    _ = (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc)) /
        ((∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
          * (d 0 * d (Fin.last n))) := by
      rw [div_mul_eq_div_div, div_self hQ.ne', one_div]
    _ ≤ _ := div_le_div_of_nonneg_right hnum (mul_pos hQ hmpos).le

end GlobalTheory.WigSh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvSqLeWignerCoeffSqRaisingStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_sq_le_wignerCoeffSqRaising : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ), StrictAnti L → (∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) → (∀ j, M j ≠ L l + 1) → 1 ≤ D → ((L 0 : ℝ) - L l ≤ D) → ((L l : ℝ) - L (Fin.last n) ≤ D) → (D ^ 2)⁻¹ ≤ GlobalTheory.WigSh.wP L M l := by
  first | exact @GlobalTheory.WigSh.inv_sq_le_wP | exact GlobalTheory.WigSh.inv_sq_le_wP | (intros; apply GlobalTheory.WigSh.inv_sq_le_wP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvSqLeWignerCoeffSqLowering
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvSqLeWignerCoeffSqLowering
open Finset

noncomputable section

namespace GlobalTheory.WigSh.LowerBound

private theorem prod_erase_succAbove {n : ℕ} (f : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    ∏ j ∈ univ.erase l, f j = ∏ j : Fin n, f (l.succAbove j) := by
  rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ]
  · rw [Finset.prod_image]
    intro a _ b _ hab
    exact Fin.succAbove_right_injective hab

private theorem ratio_pos_case {a b c : ℝ} (hb : 0 < b) (h : c ≤ a) :
    c * b / b ^ 2 ≤ a / b := by
  have : c * b / b ^ 2 = c / b := by field_simp
  rw [this]
  exact div_le_div_of_nonneg_right h hb.le

private theorem factor_lower {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (l : Fin (n + 1))
    (hs : StrictAnti L) (j : Fin n) (h1 : L j.succ < M j) (h2 : M j ≤ L j.castSucc)
    (h3 : M j ≠ L l) (G : Fin (n + 1) → ℤ)
    (hG : ∀ i, G i = max 1 (max (L i - L l) (L l - L i))) :
    (G j.succ : ℝ) * G j.castSucc / (G (l.succAbove j) : ℝ) ^ 2 ≤
      ((M j : ℝ) - L l) / ((L (l.succAbove j) : ℝ) - L l) := by
  have g1 := hG j.succ
  have g2 := hG j.castSucc
  rcases lt_or_ge j.castSucc l with hl | hl
  · rw [Fin.succAbove_of_castSucc_lt _ _ hl]
    have a1 : L l < L j.castSucc := hs hl
    have a2 : L l ≤ L j.succ := hs.antitone (Fin.castSucc_lt_iff_succ_le.1 hl)
    have e : G j.castSucc = L j.castSucc - L l := by omega
    have e' : (L j.castSucc : ℝ) - L l = G j.castSucc := by rw [e]; push_cast; ring
    rw [e']
    apply ratio_pos_case
    · have : (0 : ℤ) < G j.castSucc := by omega
      exact_mod_cast this
    · have : G j.succ ≤ M j - L l := by omega
      exact_mod_cast this
  · rw [Fin.succAbove_of_le_castSucc _ _ hl]
    have a2 : L j.castSucc ≤ L l := hs.antitone hl
    have e : G j.succ = L l - L j.succ := by omega
    have e' : (L j.succ : ℝ) - L l = -G j.succ := by rw [e]; push_cast; ring
    rw [e', div_neg, ← neg_div, mul_comm]
    apply ratio_pos_case
    · have : (0 : ℤ) < G j.succ := by omega
      exact_mod_cast this
    · have : G j.castSucc ≤ -(M j - L l) := by omega
      exact_mod_cast this

end GlobalTheory.WigSh.LowerBound

namespace GlobalTheory.WigSh

open LowerBound

theorem inv_sq_le_wM (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ)
    (hs : StrictAnti L) (hbox : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc)
    (hne : ∀ j, M j ≠ L l) (hD : 1 ≤ D) (h0 : (L 0 : ℝ) - L l ≤ D)
    (hlast : (L l : ℝ) - L (Fin.last n) ≤ D) : (D ^ 2)⁻¹ ≤ GlobalTheory.WigSh.wM L M l := by
  set G : Fin (n + 1) → ℤ := fun i => max 1 (max (L i - L l) (L l - L i)) with hGdef
  have hG : ∀ i, G i = max 1 (max (L i - L l) (L l - L i)) := fun i => rfl
  have hpos : ∀ i, (0 : ℝ) < G i := fun i => by
    have : (0 : ℤ) < G i := by rw [hG]; omega
    exact_mod_cast this
  have hl : G l = 1 := by rw [hG]; omega
  have hG0 : (G 0 : ℝ) ≤ D := by
    have a : L l ≤ L 0 := hs.antitone (Fin.zero_le l)
    have : G 0 = 1 ∨ G 0 = L 0 - L l := by rw [hG]; omega
    rcases this with e | e <;> rw [e] <;> push_cast <;> assumption
  have hGl : (G (Fin.last n) : ℝ) ≤ D := by
    have a : L (Fin.last n) ≤ L l := hs.antitone (Fin.le_last l)
    have : G (Fin.last n) = 1 ∨ G (Fin.last n) = L l - L (Fin.last n) := by rw [hG]; omega
    rcases this with e | e <;> rw [e] <;> push_cast <;> assumption
  set P : ℝ := ∏ i, (G i : ℝ) with hP
  have hPpos : 0 < P := Finset.prod_pos fun i _ => hpos i
  have p1 : ∏ j : Fin n, (G j.succ : ℝ) = P / G 0 := by
    rw [eq_div_iff (hpos 0).ne', hP, Fin.prod_univ_succ, mul_comm]
  have p2 : ∏ j : Fin n, (G j.castSucc : ℝ) = P / G (Fin.last n) := by
    rw [eq_div_iff (hpos _).ne', hP, Fin.prod_univ_castSucc]
  have p3 : ∏ j : Fin n, (G (l.succAbove j) : ℝ) = P := by
    rw [hP, Fin.prod_univ_succAbove _ l, hl]; simp
  unfold wM
  rw [prod_erase_succAbove, ← Finset.prod_div_distrib]
  refine le_trans ?_ (Finset.prod_le_prod₀
    (f := fun j : Fin n => (G j.succ : ℝ) * G j.castSucc / (G (l.succAbove j) : ℝ) ^ 2)
    (fun j _ => ?_) (fun j _ => factor_lower l hs j (hbox j).1 (hbox j).2 (hne j) G hG))
  · rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow, p1, p2, p3]
    have q0 := hpos 0
    have ql := hpos (Fin.last n)
    have : P / G 0 * (P / G (Fin.last n)) / P ^ 2 = ((G 0 : ℝ) * G (Fin.last n))⁻¹ := by
      field_simp
    rw [this]
    apply inv_anti₀ (mul_pos q0 ql)
    rw [sq]
    exact mul_le_mul hG0 hGl ql.le (by linarith)
  · have := hpos j.succ
    have := hpos j.castSucc
    positivity

end GlobalTheory.WigSh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvSqLeWignerCoeffSqLoweringStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_sq_le_wignerCoeffSqLowering : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ), StrictAnti L → (∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) → (∀ j, M j ≠ L l) → 1 ≤ D → ((L 0 : ℝ) - L l ≤ D) → ((L l : ℝ) - L (Fin.last n) ≤ D) → (D ^ 2)⁻¹ ≤ GlobalTheory.WigSh.wM L M l := by
  first | exact @GlobalTheory.WigSh.inv_sq_le_wM | exact GlobalTheory.WigSh.inv_sq_le_wM | (intros; apply GlobalTheory.WigSh.inv_sq_le_wM <;> assumption)
end
end

open Finset

namespace GlobalTheory.WigSh

private theorem strictAnti_of_box {n : ℕ} {L : Fin (n+1) → ℤ} {M : Fin n → ℤ}
    (h : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) : StrictAnti L :=
  Fin.strictAnti_iff_succ_lt.2 fun j => (h j).1.trans_le (h j).2

private theorem chain_prod_le {n₀ : ℕ} {D : ℝ} (hD : 1 ≤ D) (f : ℕ → ℝ)
    (hf : ∀ j < n₀, (D ^ 2)⁻¹ ≤ f j) : (D ^ (2 * n₀))⁻¹ ≤ ∏ j ∈ Finset.range n₀, f j := by
  have h1 : (D ^ (2 * n₀))⁻¹ = ∏ _j ∈ Finset.range n₀, (D ^ 2)⁻¹ := by
    rw [Finset.prod_const, Finset.card_range, pow_mul, inv_pow]
  rw [h1]
  exact Finset.prod_le_prod₀ (fun _ _ => by positivity)
    (fun j hj => hf j (Finset.mem_range.1 hj))

theorem chain_lower_bound : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (i : Fin n) (n₀ : ℕ) (b : ℝ), StrictAnti L → (∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) → L i.succ + 2 * (n₀ : ℤ) + 1 ≤ L i.castSucc → 1 ≤ b → (n₀ : ℝ) ≤ b → ((L 0 : ℝ) - L (Fin.last n) ≤ 2 * b) → (((3 * b) ^ (2 * n₀))⁻¹ ≤ ∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wP (Function.update L i.succ (L i.succ + (j : ℤ))) M i.succ) ∨ (((3 * b) ^ (2 * n₀))⁻¹ ≤ ∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wM (Function.update L i.castSucc (L i.castSucc - (j : ℤ))) M i.castSucc) := by
  intro n L M i n₀ b hL hbox hgap hb hn hspan
  have hD : (1 : ℝ) ≤ 3 * b := by linarith
  have h0 : ∀ k, (L k : ℝ) ≤ L 0 := fun k => by
    exact_mod_cast hL.antitone (Fin.zero_le k)
  have hl : ∀ k, (L (Fin.last n) : ℝ) ≤ L k := fun k => by
    exact_mod_cast hL.antitone (Fin.le_last k)
  have hlt : ∀ k : Fin n, k < i → L i.castSucc < M k := fun k hk =>
    lt_of_le_of_lt (hL.antitone (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hk)) (hbox k).1
  have hgt : ∀ k : Fin n, i < k → M k ≤ L i.succ := fun k hk =>
    le_trans (hbox k).2 (hL.antitone (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hk))
  by_cases hc : L i.succ + n₀ + 1 ≤ M i
  · left
    refine chain_prod_le hD _ fun j hj => ?_
    have hjZ : (j : ℤ) < n₀ := by exact_mod_cast hj
    have hjR : (j : ℝ) ≤ b := le_trans (by exact_mod_cast hj.le) hn
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hbox' : ∀ k : Fin n, Function.update L i.succ (L i.succ + (j : ℤ)) k.succ < M k ∧
        M k ≤ Function.update L i.succ (L i.succ + (j : ℤ)) k.castSucc := by
      intro k
      constructor
      · by_cases hk : k = i
        · subst hk
          rw [Function.update_self]; omega
        · rw [Function.update_of_ne (fun h => hk (Fin.succ_injective _ h))]
          exact (hbox k).1
      · by_cases hk : k.castSucc = i.succ
        · have := (hbox k).2
          rw [hk] at this ⊢
          rw [Function.update_self]; omega
        · rw [Function.update_of_ne hk]
          exact (hbox k).2
    refine GlobalTheory.T.inv_sq_le_wignerCoeffSqRaising n _ M i.succ (3 * b) (strictAnti_of_box hbox') hbox' ?_ hD ?_ ?_
    · intro k
      rw [Function.update_self]
      rcases lt_trichotomy k i with hk | hk | hk
      · have := hlt k hk; omega
      · subst hk; omega
      · have := hgt k hk; omega
    · rw [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      push_cast
      have := hl i.succ
      linarith
    · rw [Function.update_self]
      by_cases hk : Fin.last n = i.succ
      · rw [hk, Function.update_self]; linarith
      · rw [Function.update_of_ne hk]
        push_cast
        have := h0 i.succ
        linarith
  · right
    refine chain_prod_le hD _ fun j hj => ?_
    have hjZ : (j : ℤ) < n₀ := by exact_mod_cast hj
    have hjR : (j : ℝ) ≤ b := le_trans (by exact_mod_cast hj.le) hn
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hbox' : ∀ k : Fin n,
        Function.update L i.castSucc (L i.castSucc - (j : ℤ)) k.succ < M k ∧
        M k ≤ Function.update L i.castSucc (L i.castSucc - (j : ℤ)) k.castSucc := by
      intro k
      constructor
      · by_cases hk : k.succ = i.castSucc
        · have hki : k < i := by
            have := congrArg Fin.val hk
            simp only [Fin.val_succ, Fin.val_castSucc] at this
            rw [Fin.lt_def]; omega
          have := hlt k hki
          rw [hk, Function.update_self]; omega
        · rw [Function.update_of_ne hk]
          exact (hbox k).1
      · by_cases hk : k = i
        · subst hk
          rw [Function.update_self]; omega
        · rw [Function.update_of_ne (fun h => hk (Fin.castSucc_injective _ h))]
          exact (hbox k).2
    refine GlobalTheory.T.inv_sq_le_wignerCoeffSqLowering n _ M i.castSucc (3 * b) (strictAnti_of_box hbox') hbox' ?_ hD ?_ ?_
    · intro k
      rw [Function.update_self]
      rcases lt_trichotomy k i with hk | hk | hk
      · have := hlt k hk; omega
      · subst hk; omega
      · have := hgt k hk; omega
    · rw [Function.update_self]
      by_cases hk : 0 = i.castSucc
      · rw [hk, Function.update_self]; linarith
      · rw [Function.update_of_ne hk]
        push_cast
        have := hl i.castSucc
        linarith
    · rw [Function.update_self, Function.update_of_ne (Fin.castSucc_lt_last i).ne']
      push_cast
      have := h0 i.castSucc
      linarith

end GlobalTheory.WigSh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqAdjointAddGeOfJointEigenspaces
namespace GlobalTheory

open scoped InnerProductSpace

theorem norm_sq_adjoint_add_ge_of_joint_eigenspaces (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (ι : Type) (S : ι → Submodule ℂ V) (A : Vp →L[ℂ] V) (B : Vm →L[ℂ] V) (wp wm : ι → ℝ) (c : ℝ) (hS : (⨆ i, S i) = ⊤)
    (hw : ∀ i, ∀ v ∈ S i, A (ContinuousLinearMap.adjoint A v) = (wp i : ℂ) • v ∧ B (ContinuousLinearMap.adjoint B v) = (wm i : ℂ) • v)
    (hc : ∀ i, c ≤ wp i ∨ c ≤ wm i) (v : V) :
    c * ‖v‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint A v‖ ^ 2 + ‖ContinuousLinearMap.adjoint B v‖ ^ 2 := by
  have hA : ∀ x : V, (⟪A (ContinuousLinearMap.adjoint A x), x⟫_ℂ).re = ‖ContinuousLinearMap.adjoint A x‖ ^ 2 := by
    intro x
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hB : ∀ x : V, (⟪B (ContinuousLinearMap.adjoint B x), x⟫_ℂ).re = ‖ContinuousLinearMap.adjoint B x‖ ^ 2 := by
    intro x
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hsm : ∀ (r : ℝ) (x : V), (⟪(r : ℂ) • x, x⟫_ℂ).re = r * ‖x‖ ^ 2 := by
    intro r x
    rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]
    congr 1
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  let X : V →ₗ[ℂ] V := (A ∘L ContinuousLinearMap.adjoint A + B ∘L ContinuousLinearMap.adjoint B : V →L[ℂ] V).toLinearMap
  have hX : ∀ x, X x = A (ContinuousLinearMap.adjoint A x) + B (ContinuousLinearMap.adjoint B x) := fun x => rfl
  have hsym : X.IsSymmetric := by
    intro x y
    rw [hX, hX, inner_add_left, inner_add_right]
    rw [← ContinuousLinearMap.adjoint_inner_right A, ← ContinuousLinearMap.adjoint_inner_right B,
      ← ContinuousLinearMap.adjoint_inner_left A, ← ContinuousLinearMap.adjoint_inner_left B]
  have hge : ∀ i, ∀ x ∈ S i, x ≠ 0 → c ≤ wp i + wm i := by
    intro i x hx hx0
    have hn : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
    have h1 := hA x
    have h2 := hB x
    rw [(hw i x hx).1, hsm] at h1
    rw [(hw i x hx).2, hsm] at h2
    have p1 : 0 ≤ wp i := by
      have : 0 ≤ wp i * ‖x‖ ^ 2 := by rw [h1]; positivity
      exact nonneg_of_mul_nonneg_left this hn
    have p2 : 0 ≤ wm i := by
      have : 0 ≤ wm i * ‖x‖ ^ 2 := by rw [h2]; positivity
      exact nonneg_of_mul_nonneg_left this hn
    rcases hc i with h | h <;> linarith
  have hev : ∀ (μ : ℝ) (e : V), X e = (μ : ℂ) • e → e ≠ 0 → c ≤ μ := by
    intro μ e he he0
    by_contra hlt
    apply he0
    have hmem : e ∈ (⨆ i, S i)ᗮ := by
      rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro i
      rw [Submodule.mem_orthogonal]
      intro x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      have hle := hge i x hx hx0
      have hXx : X x = ((wp i + wm i : ℝ) : ℂ) • x := by
        rw [hX, (hw i x hx).1, (hw i x hx).2, ← add_smul]; push_cast; rfl
      have h := hsym x e
      rw [hXx, he, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
      have hne : ((wp i + wm i : ℝ) : ℂ) ≠ (μ : ℂ) := by
        intro h'
        have := Complex.ofReal_injective h'
        apply hlt; linarith
      by_contra h0
      exact hne (mul_right_cancel₀ h0 h)
    rw [hS, Submodule.top_orthogonal_eq_bot] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  have hn : Module.finrank ℂ V = Module.finrank ℂ V := rfl
  set b := hsym.eigenvectorBasis hn with hb
  have hμ : ∀ j, c ≤ hsym.eigenvalues hn j := fun j =>
    hev _ (b j) (hsym.apply_eigenvectorBasis hn j) (b.orthonormal.ne_zero j)
  rw [← hA, ← hB, ← Complex.add_re, ← inner_add_left, ← hX]
  rw [← b.sum_inner_mul_inner (X v) v, Complex.re_sum, ← b.sum_sq_norm_inner_right v, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : ⟪X v, b j⟫_ℂ = (hsym.eigenvalues hn j : ℂ) * ⟪v, b j⟫_ℂ := by
    rw [hsym v (b j), hb, hsym.apply_eigenvectorBasis hn j, inner_smul_right]; rfl
  rw [h1, mul_assoc, Complex.re_ofReal_mul, ← inner_conj_symm v (b j), Complex.conj_mul']
  have : ((‖⟪b j, v⟫_ℂ‖ : ℂ) ^ 2).re = ‖⟪b j, v⟫_ℂ‖ ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [this]
  exact mul_le_mul_of_nonneg_right (hμ j) (sq_nonneg _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntCoordsOfRegularParam
namespace GlobalTheory

theorem exists_int_coords_of_regular_param (n : ℕ) (u : ℕ → ℝ)
    (h : ∀ i ∈ Finset.Icc 1 n, ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) :
    ∃ (β : ℂ) (L : Fin (n + 1) → ℤ), StrictAnti L ∧
      (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) ∧
      ∀ i j : Fin (n + 1), (L i : ℝ) - (L j : ℝ) = u ((i : ℕ) + 1) - u ((j : ℕ) + 1) := by
  have key : ∀ j : ℕ, j ≤ n → ∃ z : ℤ, (z : ℝ) = u (j + 1) - u 1 := by
    intro j
    induction j with
    | zero => intro _; exact ⟨0, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨z, hz⟩ := ih (by omega)
      obtain ⟨N, hN⟩ := h (k + 1) (Finset.mem_Icc.2 ⟨by omega, hk⟩)
      refine ⟨z - N - 1, ?_⟩
      push_cast
      linarith
  choose z hz using key
  refine ⟨(u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2, fun j => z j (Nat.lt_succ_iff.1 j.2), ?_, ?_, ?_⟩
  · rw [Fin.strictAnti_iff_succ_lt]
    intro i
    obtain ⟨N, hN⟩ := h (i + 1) (Finset.mem_Icc.2 ⟨by omega, i.2⟩)
    have h1 := hz (i.succ : Fin (n + 1)) (Nat.lt_succ_iff.1 i.succ.2)
    have h2 := hz (i.castSucc : Fin (n + 1)) (Nat.lt_succ_iff.1 i.castSucc.2)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : ((z (i.succ : Fin (n + 1)) (Nat.lt_succ_iff.1 i.succ.2) : ℤ) : ℝ)
        < (z (i.castSucc : Fin (n + 1)) (Nat.lt_succ_iff.1 i.castSucc.2) : ℤ) := by
      rw [h1, h2]
      simp only [Fin.val_succ, Fin.val_castSucc]
      linarith
    exact_mod_cast this
  · intro j
    have h1 := congrArg (fun x : ℝ => (x : ℂ)) (hz j (Nat.lt_succ_iff.1 j.2))
    simp only [Complex.ofReal_intCast, Complex.ofReal_sub] at h1
    simp only [h1]
    ring
  · intro i j
    simp only [hz]
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedTypesLowerBound
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem exists_shifted_types_lower_bound : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (u : ℕ → ℝ) (l n₀ : ℕ) (b : ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) → 1 ≤ l → l < k → 2 * (n₀ : ℝ) + 1 ≤ u l - u (l + 1) → (∀ i ∈ Finset.Icc 1 k, |u i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b → ∃ (Vp : Type) (_ : NormedAddCommGroup Vp) (_ : InnerProductSpace ℂ Vp) (_ : FiniteDimensional ℂ Vp) (Vm : Type) (_ : NormedAddCommGroup Vm) (_ : InnerProductSpace ℂ Vm) (_ : FiniteDimensional ℂ Vm) (πp : Mx k r → (Vp →L[ℂ] Vp)) (πm : Mx k r → (Vm →L[ℂ] Vm)) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Vm →L[ℂ] V)), IsType k r z πp (Function.update u (l + 1) (u (l + 1) + (n₀ : ℝ))) ∧ IsType k r z πm (Function.update u l (u l - (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap k r z πp π n₀ Ap ∧ GlobalTheory.WigSh.WigMap k r z πm π n₀ Am ∧ ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ∀ v : V, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  intro V _ _ _ k r z π u l n₀ b hz hT hπ hreg hl1 hlk hgap hb hn hb1
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have hm : m < n := by omega
  let i : Fin n := ⟨m, hm⟩
  obtain ⟨β, L, hL, hu, hd⟩ := GlobalTheory.exists_int_coords_of_regular_param n u (by simpa using hreg)
  obtain ⟨B, hB⟩ := (GlobalTheory.frame_exists_and_vector_eq_smul_translate n r z hz hT).1
  have hgapZ : L i.succ + 2 * (n₀ : ℤ) + 1 ≤ L i.castSucc := by
    have h := hd i.castSucc i.succ
    simp only [Fin.val_succ, Fin.val_castSucc, i] at h
    have : ((L i.succ + 2 * (n₀ : ℤ) + 1 : ℤ) : ℝ) ≤ ((L i.castSucc : ℤ) : ℝ) := by
      push_cast
      simp only [i]
      linarith
    exact_mod_cast this
  have hwide : (L 0 : ℝ) - (L (Fin.last n) : ℝ) ≤ 2 * b := by
    rw [hd]
    have h1 := abs_le.mp (hb (((0 : Fin (n + 1)) : ℕ) + 1) (by simp))
    have h2 := abs_le.mp (hb (((Fin.last n : Fin (n + 1)) : ℕ) + 1) (by simp))
    linarith [h1.2, h2.1]
  obtain ⟨Vp, iP1, iP2, iP3, πp, Ap, hπp, hAp, hwp⟩ :=
    GlobalTheory.T.exists_wignerContraction_chain_raising V n r z π u β L B i.succ n₀ hz hT hπ hL hu hB (by
      intro j hj
      have hj' : j ≤ i.castSucc := Fin.le_castSucc_iff.mpr hj
      have := hL.antitone hj'
      omega)
  obtain ⟨Vm, familyMassRatio, familyMassSecondLine, iM3, πm, Am, hπm, hAm, hwm⟩ :=
    GlobalTheory.T.exists_wignerContraction_chain_lowering V n r z π u β L B i.castSucc n₀ hz hT hπ hL hu hB (by
      intro j hj
      have hj' : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp hj
      have := hL.antitone hj'
      omega)
  refine ⟨Vp, iP1, iP2, iP3, Vm, familyMassRatio, familyMassSecondLine, iM3, πp, πm, Ap, Am, hπp, hπm, hAp, hAm, ?_⟩
  refine GlobalTheory.WigSh.lower_bound_spreads V Vp Vm n r z π πp πm B Ap Am n₀ b hz hT hπ.2.2.2.1 hπp.2.2.2.1
    hπm.2.2.2.1 hB hAp hAm ?_
  intro v
  have hyp := (GlobalTheory.TypeGlModule.hyp_and_adj V n r z π u β L B hz hT hπ hL hu hB).1
  have hdec := (Formalism.FourierDecayAlt.P.branching_decomposition V n (EB π B) β L hyp).2
  have hspan : ⨆ M : {M : Fin n → ℤ // Box L M}, CapSp (subA (EB π B)) (shf β M.1) = ⊤ := by
    rw [← hdec, iSup_subtype]
  have key := GlobalTheory.norm_sq_adjoint_add_ge_of_joint_eigenspaces V Vp Vm {M : Fin n → ℤ // Box L M}
    (fun M => CapSp (subA (EB π B)) (shf β M.1)) (Ap (B (Fin.last n))) (Am (B (Fin.last n))) _ _
    ((3 * b) ^ (2 * n₀))⁻¹ hspan (fun M w hw => ⟨hwp M.1 w hw, hwm M.1 w hw⟩)
    (fun M => GlobalTheory.WigSh.chain_lower_bound n L M.1 i n₀ b hL M.2 hgapZ hb1 hn hwide) v
  have hpos : 0 < (3 * b) ^ (2 * n₀) := by positivity
  rwa [inv_mul_le_iff₀ hpos] at key

end GlobalTheory.WigSh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsShiftedTypesLowerBoundStatement
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shifted_types_lower_bound_alt : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (u : ℕ → ℝ) (l n₀ : ℕ) (b : ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) → 1 ≤ l → l < k → 2 * (n₀ : ℝ) + 1 ≤ u l - u (l + 1) → (∀ i ∈ Finset.Icc 1 k, |u i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b → ∃ (Vp : Type) (_ : NormedAddCommGroup Vp) (_ : InnerProductSpace ℂ Vp) (_ : FiniteDimensional ℂ Vp) (Vm : Type) (_ : NormedAddCommGroup Vm) (_ : InnerProductSpace ℂ Vm) (_ : FiniteDimensional ℂ Vm) (πp : Mx k r → (Vp →L[ℂ] Vp)) (πm : Mx k r → (Vm →L[ℂ] Vm)) (Ap : (Fin (2 * r + k + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Vm →L[ℂ] V)), IsType k r z πp (Function.update u (l + 1) (u (l + 1) + (n₀ : ℝ))) ∧ IsType k r z πm (Function.update u l (u l - (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap k r z πp π n₀ Ap ∧ GlobalTheory.WigSh.WigMap k r z πm π n₀ Am ∧ ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ∀ v : V, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  first | exact @GlobalTheory.WigSh.exists_shifted_types_lower_bound | exact GlobalTheory.WigSh.exists_shifted_types_lower_bound | (intros; apply GlobalTheory.WigSh.exists_shifted_types_lower_bound <;> assumption)
end
