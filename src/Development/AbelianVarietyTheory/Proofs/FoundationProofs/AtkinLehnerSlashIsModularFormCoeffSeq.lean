module

public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGammaOneOfCoeffSeq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthAlgebraSlashStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerSlashInverseCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerSlashInverseCharacter
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem atkinLehner_conj_int (N l : ℕ) (a b c d : ℤ) (h : (N : ℤ) * a * d - l * b * c = 1) (γ : M2)
    (hγ : ((N * l : ℕ) : ℤ) ∣ γ 1 0) (hdet : γ.det = 1) :
    ∃ γ' : M2, !![(N : ℤ) * a, b; N * l * c, N * d] * γ = γ' * !![(N : ℤ) * a, b; N * l * c, N * d] ∧
    γ'.det = 1 ∧ ((N * l : ℕ) : ℤ) ∣ γ' 1 0 ∧ (N : ℤ) ∣ γ' 1 1 - γ 0 0 := by
  obtain ⟨r, hr⟩ := hγ
  push_cast at hr
  set p := γ 0 0
  set q := γ 0 1
  set s := γ 1 1
  have hdet' : p * s - (N * l * r) * q = 1 := by
    rw [Matrix.det_fin_two] at hdet; rw [hr] at hdet; linarith
  refine ⟨!![(N : ℤ) * a * d * p + N * l * b * d * r - N * l * a * c * q - l * b * c * s,
     -(a * b * p) - l * b * b * r + N * a * a * q + a * b * s;
     N * l * (c * d * p + N * d * d * r - l * c * c * q - c * d * s),
     -(l * b * c * p) - N * l * b * d * r + N * l * a * c * q + N * a * d * s], ?_, ?_, ?_, ?_⟩
  · have hγe : γ = !![p, q; N * l * r, s] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [p, q, s, hr]
    rw [hγe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination -(N * a * p + b * N * l * r) * h
    · linear_combination -(N * a * q + b * s) * h
    · linear_combination -(N * l * c * p + N * d * N * l * r) * h
    · linear_combination -(N * l * c * q + N * d * s) * h
  · rw [Matrix.det_fin_two_of]
    linear_combination ((N : ℤ) * a * d - l * b * c) ^ 2 * hdet' + ((N : ℤ) * a * d - l * b * c + 1) * h
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    push_cast
    exact Dvd.intro _ rfl
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    exact ⟨-(b * d * l * r) + l * a * c * q + a * d * s - a * d * p, by linear_combination p * h⟩

theorem inv_slz_atkinLehner : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) (a₀ b₀ c₀ d₀ : ℤ),
    N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → Inv k (N * l) (ch χ) f →
    Inv k (N * l) (ch χ⁻¹) (slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] f) := by
  intro k N l χ f a b c d h hk hN hf
  set Q : M2 := !![(N : ℤ) * a, b; N * l * c, N * d] with hQ
  have hQdet : 0 < Q.det := by
    have : Q.det = N * (N * a * d - l * b * c) := by rw [hQ, Matrix.det_fin_two_of]; ring
    rw [this, h, mul_one]; exact_mod_cast hN
  have hiff := (slz_props k (slz k Q f) hk).2.2.1 (N * l) (ch χ⁻¹)
  have hiff0 := (slz_props k f hk).2.2.1 (N * l) (ch χ)
  refine hiff.2 fun γ hγ => ?_
  have hγdet : (γ : M2).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  have hγ' : ((N * l : ℕ) : ℤ) ∣ (γ : M2) 1 0 := by exact_mod_cast hγ
  obtain ⟨g, hg, hgdet, hgdvd, hgcong⟩ := atkinLehner_conj_int N l a b c d h (γ : M2) hγ' hγdet
  let γ₁ : SL(2, ℤ) := ⟨g, hgdet⟩
  have hf1 := hiff0.1 hf γ₁ (by exact_mod_cast hgdvd)
  have hcalc : slz k (γ : M2) (slz k Q f) = slz k Q (slz k (γ₁ : M2) f) := by
    rw [← slz_mul k f Q (γ : M2) hQdet (by rw [hγdet]; exact one_pos), hg,
      slz_mul k f g Q (by rw [hgdet]; exact one_pos) hQdet]
  rw [hcalc, hf1]
  have hchar : ch χ (γ₁ 1 1) = ch χ⁻¹ (γ 1 1) := by
    simp only [ch]
    have e1 : ((γ₁ 1 1 : ℤ) : ZMod N) = ((γ 0 0 : ℤ) : ZMod N) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (by
        have : (N : ℤ) ∣ g 1 1 - γ 0 0 := hgcong
        rw [← dvd_neg, neg_sub]; exact this)
    have e2 : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have hd := hγdet
      rw [Matrix.det_fin_two] at hd
      obtain ⟨r, hr⟩ := hγ'
      have : ((((γ : M2) 0 0 * (γ : M2) 1 1 - (γ : M2) 0 1 * (γ : M2) 1 0 : ℤ)) : ZMod N) = 1 := by
        rw [hd]; simp
      rw [hr] at this
      push_cast at this
      simpa using this
    rw [e1, MulChar.inv_apply_eq_inv']
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, e2, map_one]
  funext τ
  simp only [slz]
  rw [hchar]
  ring

end GlobalTheory.EisM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerSlashInverseCharacterStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atkinLehner_slash_inverse_character : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → Inv k (N * l) (ch χ) f → Inv k (N * l) (ch χ⁻¹) (slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] f) := by
  first | exact @GlobalTheory.EisM.inv_slz_atkinLehner | exact GlobalTheory.EisM.inv_slz_atkinLehner | (intros; apply GlobalTheory.EisM.inv_slz_atkinLehner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerSlashIsModularFormCoeffSeq
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.AtkinLehnerForm

theorem toGL_entry (A : M2) (hA : A.det ≠ 0) (i j : Fin 2) :
    (↑(GlobalTheory.HeckeFamilyMatrices.toGL A) : Matrix (Fin 2) (Fin 2) ℝ) i j = (A i j : ℝ) := by
  rw [GlobalTheory.HeckeFamilyMatrices.toGL_val A hA]; simp

theorem slz_eq_slash (k : ℕ) (hk : 1 ≤ k) (δ : M2) (hδ : 0 < δ.det) (f : ℍ → ℂ) :
    slz k δ f = f ∣[(k : ℤ)] GlobalTheory.HeckeFamilyMatrices.toGL δ := by
  funext τ
  have hd : 0 < (GlobalTheory.HeckeFamilyMatrices.toGL δ).det.val := GlobalTheory.HeckeFamilyMatrices.toGL_det_pos δ hδ
  have hpt : ofComplex ((((δ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 0 1 : ℤ) : ℂ)) / (((δ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((δ 1 1 : ℤ) : ℂ)))
      = GlobalTheory.HeckeFamilyMatrices.toGL δ • τ := by
    ext1
    rw [slzMob_coe δ hδ τ, UpperHalfPlane.coe_smul_of_det_pos hd]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, toGL_entry δ hδ.ne']
  rw [ModularForm.slash_apply, GlobalTheory.HeckeFamilyMatrices.sigma_pos hd, slz, hpt]
  have hdet : (GlobalTheory.HeckeFamilyMatrices.toGL δ).det.val = (δ.det : ℝ) := GlobalTheory.HeckeFamilyMatrices.toGL_det δ hδ.ne'
  rw [hdet, abs_of_pos (by exact_mod_cast hδ)]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e1 : (((m + 1 : ℕ) : ℤ) - 1) = ((m : ℕ) : ℤ) := by push_cast; ring
  rw [e1, zpow_natCast, zpow_neg, zpow_natCast]
  simp only [Nat.add_sub_cancel, UpperHalfPlane.denom, toGL_entry δ hδ.ne', Complex.ofReal_intCast]
  ring

end GlobalTheory.EisM.AtkinLehnerForm

namespace GlobalTheory.EisM.AtkinLehnerForm

theorem qs_add_int (a : ℕ → ℂ) (τ : ℍ) (m : ℤ) : qs a (ofComplex ((τ : ℂ) + m)) = qs a τ := by
  have him : 0 < ((τ : ℂ) + m).im := by simpa using τ.im_pos
  have hcoe : ((ofComplex ((τ : ℂ) + m) : ℍ) : ℂ) = (τ : ℂ) + m := by
    rw [ofComplex_apply_of_im_pos him]
  simp only [qs, hcoe]
  congr 1
  funext n
  have e : cexp (2 * π * Complex.I * n * ((τ : ℂ) + m)) = cexp (2 * π * Complex.I * n * τ) := by
    rw [show 2 * π * Complex.I * n * ((τ : ℂ) + m) = 2 * π * Complex.I * n * τ + ((n * m : ℤ) : ℂ) * (2 * π * Complex.I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [e]

theorem slz_levelOne (k : ℕ) (a : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ) (h : a₀ * d₀ = 1) :
    slz k !![((1 : ℕ) : ℤ) * a₀, b₀; ((1 : ℕ) : ℤ) * ((0 : ℕ) : ℤ) * c₀, ((1 : ℕ) : ℤ) * d₀] (qs a)
      = fun τ => ((d₀ : ℂ) ^ k)⁻¹ * qs a τ := by
  funext τ
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e : (((((1 : ℕ) : ℤ) * 1 : ℤ) : ℂ) * (τ : ℂ) + ((b₀ : ℤ) : ℂ)) / (((((1 : ℕ) : ℤ) * ((0 : ℕ) : ℤ) * c₀ : ℤ) : ℂ) * (τ : ℂ) + ((((1 : ℕ) : ℤ) * 1 : ℤ) : ℂ))
        = (τ : ℂ) + ((b₀ : ℤ) : ℂ) := by push_cast; ring
    simp only [slz, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.det_fin_two_of, e, qs_add_int]
    push_cast
    try simp
  · have e : (((((1 : ℕ) : ℤ) * (-1) : ℤ) : ℂ) * (τ : ℂ) + ((b₀ : ℤ) : ℂ)) / (((((1 : ℕ) : ℤ) * ((0 : ℕ) : ℤ) * c₀ : ℤ) : ℂ) * (τ : ℂ) + ((((1 : ℕ) : ℤ) * (-1) : ℤ) : ℂ))
        = (τ : ℂ) + ((-b₀ : ℤ) : ℂ) := by push_cast; ring
    simp only [slz, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.det_fin_two_of, e, qs_add_int]
    push_cast
    try simp

end GlobalTheory.EisM.AtkinLehnerForm


open GlobalTheory.EisM.AtkinLehnerForm in
theorem GlobalTheory.EisM.atkinLehner_MF : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → MF k (N * l) (ch χ) a → ∃ a' : ℕ → ℂ, MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) := by
  intro k N l χ a a₀ b₀ c₀ d₀ h hk hN ha
  have hinv := GlobalTheory.T.atkinLehner_slash_inverse_character k N l χ (qs a) a₀ b₀ c₀ d₀ h hk hN ha.2
  suffices hex : ∃ a' : ℕ → ℂ, PolyB a' ∧ qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) by
    obtain ⟨a', h1, h2⟩ := hex
    exact ⟨a', ⟨h1, h2 ▸ hinv⟩, h2⟩
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have h' : (N : ℤ) * (a₀ * d₀) = 1 := by linear_combination h
    have hN1 : N = 1 := by exact_mod_cast Int.eq_one_of_mul_eq_one_right (by positivity) h'
    subst hN1
    have had : a₀ * d₀ = 1 := by simpa using h'
    rw [slz_levelOne k a a₀ b₀ c₀ d₀ had]
    obtain ⟨C, A, hC⟩ := ha.1
    refine ⟨fun n => ((d₀ : ℂ) ^ k)⁻¹ * a n, ⟨‖((d₀ : ℂ) ^ k)⁻¹‖ * C, A, fun n => ?_⟩, ?_⟩
    · rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)
    · funext τ
      simp only [qs]
      rw [← tsum_mul_left]
      congr 1
      funext n
      ring
  · set δ : M2 := !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] with hδdef
    have hdet : δ.det = N := by rw [hδdef, Matrix.det_fin_two_of]; linear_combination (N : ℤ) * h
    have hδ : 0 < δ.det := by rw [hdet]; exact_mod_cast hN
    have hL : 0 < N * l := Nat.mul_pos hN hl
    haveI : NeZero (N * l) := ⟨hL.ne'⟩
    obtain ⟨f, hf⟩ := GlobalTheory.EisM.modularForm_gammaOne_of_MF k (N * l) N χ a hL (dvd_mul_right N l) ha
    have hF : slz k δ (qs a) = ⇑f ∣[(k : ℤ)] GlobalTheory.HeckeFamilyMatrices.toGL δ := by rw [hf]; exact slz_eq_slash k hk δ hδ _
    let F : ModularForm (Gamma1 (N * l)) (k : ℤ) :=
      { toFun := slz k δ (qs a)
        slash_action_eq' := by
          rintro _ ⟨A, (hA : A ∈ Gamma1 (N * l)), rfl⟩
          exact GlobalTheory.EisM.OnGammaOne.slash_inv (dvd_mul_right N l) hinv A hA
        holo' := by
          show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (slz k δ (qs a))
          rw [hF]; exact (ModularFormClass.holo f).slash _ _
        bdd_at_cusps' := by
          intro c hc
          show c.IsBoundedAt (slz k δ (qs a)) (k : ℤ)
          rw [hF, ← OnePoint.IsBoundedAt.smul_iff]
          apply ModularFormClass.bdd_at_cusps f
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
          exact GlobalTheory.HeckeFamilyMatrices.isCusp_SL2Z_toGL_smul δ hδ.ne' hc }
    refine ⟨coef F, ?_, qs_coef_of_mfc F⟩
    have hb := ModularFormClass.qExpansion_isBigO (Int.natCast_nonneg k) F
    simp only [strictWidthInfty_Gamma1, zpow_natCast] at hb
    exact polyB_of_isBigO hb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerSlashIsModularFormCoeffSeqStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atkinLehner_slash_isModularFormCoeffSeq : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → MF k (N * l) (ch χ) a → ∃ a' : ℕ → ℂ, MF k (N * l) (ch χ⁻¹) a' ∧ qs a' = slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) := by
  first | exact @GlobalTheory.EisM.atkinLehner_MF | exact GlobalTheory.EisM.atkinLehner_MF | (intros; apply GlobalTheory.EisM.atkinLehner_MF <;> assumption)
end
