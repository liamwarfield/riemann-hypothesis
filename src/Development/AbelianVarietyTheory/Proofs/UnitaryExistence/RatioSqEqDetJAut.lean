module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TwoDvdMultiplierOfThetaZActEqUnitMul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RatioSqEqDetJAut
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaSqLawOfZero
noncomputable section

open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThetaCharMult

variable {g : ℕ}

theorem sp_rel_transpose {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    ((cMat γ).toBlocks₁₂ * (cMat γ).toBlocks₂₁ᵀ - (cMat γ).toBlocks₁₁ * (cMat γ).toBlocks₂₂ᵀ = -1) ∧
    ((cMat γ).toBlocks₂₂ * (cMat γ).toBlocks₂₁ᵀ - (cMat γ).toBlocks₂₁ * (cMat γ).toBlocks₂₂ᵀ = 0) := by
  obtain ⟨-, r2, -, r4⟩ := sp_rel (SymplecticGroup.transpose_mem hγ)
  exact ⟨r2, r4⟩

theorem sp_rel_int {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    γ.toBlocks₁₁ * γ.toBlocks₂₂ᵀ = 1 + γ.toBlocks₁₂ * γ.toBlocks₂₁ᵀ := by
  have h := (sp_rel_transpose hγ).1
  have h' : (cMat γ).toBlocks₁₁ * (cMat γ).toBlocks₂₂ᵀ =
      1 + (cMat γ).toBlocks₁₂ * (cMat γ).toBlocks₂₁ᵀ := by
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  ext i j
  have := congrFun (congrFun h' i) j
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, cMat, Matrix.toBlocks₁₁,
    Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.map_apply] at this ⊢
  exact_mod_cast this

theorem shift_algebra (A B C D τ σ J : Matrix (Fin g) (Fin g) ℂ) (hτ : τ.IsSymm) (hσ : σ.IsSymm)
    (h1 : J * (C * τ + D) = 1) (h2 : (C * τ + D) * J = 1) (hs : σ = (A * τ + B) * J)
    (hA : A - σ * C = Jᵀ) (hCD : D * Cᵀ - C * Dᵀ = 0) (a b z a' b' : Fin g → ℂ)
    (ha' : a' = Aᵀ *ᵥ a + Cᵀ *ᵥ b) (hb' : b' = Bᵀ *ᵥ a + Dᵀ *ᵥ b) :
    Jᵀ *ᵥ (z + τ *ᵥ a' + b') = Jᵀ *ᵥ z + σ *ᵥ a + b ∧
    (z + τ *ᵥ a' + b') ⬝ᵥ ((J * C) *ᵥ (z + τ *ᵥ a' + b')) +
        2 * (-(a' ⬝ᵥ (τ *ᵥ a')) / 2 - a' ⬝ᵥ (z + b')) =
      z ⬝ᵥ ((J * C) *ᵥ z) + (a ⬝ᵥ b - a' ⬝ᵥ b') +
        2 * (-(a ⬝ᵥ (σ *ᵥ a)) / 2 - a ⬝ᵥ (Jᵀ *ᵥ z + b)) := by
  set j := C * τ + D with hj
  have hjT : jᵀ = τ * Cᵀ + Dᵀ := by rw [hj, transpose_add, transpose_mul, hτ.eq]
  have hjσ : jᵀ * σ = τ * Aᵀ + Bᵀ := by
    conv_lhs => rw [← hσ.eq]
    rw [← transpose_mul, hs, Matrix.mul_assoc, h1, Matrix.mul_one, transpose_add, transpose_mul,
      hτ.eq]
  set p := σ *ᵥ a + b with hp
  set q := τ *ᵥ a' + b' with hq
  have hqp : jᵀ *ᵥ p = q := by
    rw [hp, hq, ha', hb', mulVec_add, mulVec_mulVec, hjσ, hjT]
    simp only [add_mulVec, mulVec_add, mulVec_mulVec]
    abel
  have hpq : Jᵀ *ᵥ q = p := by
    rw [← hqp, mulVec_mulVec, ← transpose_mul, h2, transpose_one, one_mulVec]
  have hM : (J * C).IsSymm := by
    have e : C * jᵀ = j * Cᵀ := by
      rw [hjT, hj, Matrix.mul_add, Matrix.add_mul, sub_eq_zero.mp hCD, Matrix.mul_assoc]
    show (J * C)ᵀ = J * C
    calc (J * C)ᵀ = (J * j) * Cᵀ * Jᵀ := by rw [h1, Matrix.one_mul, transpose_mul]
      _ = J * (C * jᵀ) * Jᵀ := by rw [e]; simp only [Matrix.mul_assoc]
      _ = J * C * (J * j)ᵀ := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = J * C := by rw [h1, transpose_one, Matrix.mul_one]
  have hq1 : ∀ x, q ⬝ᵥ ((J * C) *ᵥ x) = a' ⬝ᵥ x - a ⬝ᵥ (Jᵀ *ᵥ x) := by
    intro x
    have e1 : q ⬝ᵥ ((J * C) *ᵥ x) = p ⬝ᵥ (C *ᵥ x) := by
      rw [← hpq, ← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]
    have e2 : a' ⬝ᵥ x = a ⬝ᵥ (A *ᵥ x) + b ⬝ᵥ (C *ᵥ x) := by
      rw [ha', add_dotProduct, mulVec_transpose, mulVec_transpose, dotProduct_mulVec,
        dotProduct_mulVec]
    have e3 : (σ *ᵥ a) ⬝ᵥ (C *ᵥ x) = a ⬝ᵥ (σ *ᵥ (C *ᵥ x)) := by
      rw [dot_mulVec_symm hσ, dotProduct_comm]
    rw [e1, e2, ← hA, sub_mulVec, dotProduct_sub, hp, add_dotProduct, e3, mulVec_mulVec]
    ring
  have hz : z + τ *ᵥ a' + b' = z + q := by rw [hq, add_assoc]
  rw [hz]
  refine ⟨by rw [mulVec_add, hpq, hp, add_assoc], ?_⟩
  have e4 := dot_mulVec_symm hM q z
  have e5 := hq1 z
  have e6 := hq1 q
  rw [hpq] at e6
  have e7 : a' ⬝ᵥ q = a' ⬝ᵥ (τ *ᵥ a') + a' ⬝ᵥ b' := by rw [hq, dotProduct_add]
  have e8 : a ⬝ᵥ p = a ⬝ᵥ (σ *ᵥ a) + a ⬝ᵥ b := by rw [hp, dotProduct_add]
  simp only [mulVec_add, add_dotProduct, dotProduct_add]
  rw [e4, e5, e6, e7, e8]
  ring

theorem dvd_mulVec {M : Matrix (Fin g) (Fin g) ℤ} {k : ℤ} (h : ∀ i j, k ∣ M i j) (v : Fin g → ℤ)
    (i : Fin g) : k ∣ (M *ᵥ v) i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => (h i j).mul_right _

theorem dvd_dot_left {k : ℤ} {u : Fin g → ℤ} (h : ∀ i, k ∣ u i) (v : Fin g → ℤ) : k ∣ u ⬝ᵥ v :=
  Finset.dvd_sum fun j _ => (h j).mul_right _

theorem dvd_dot_right {k : ℤ} {v : Fin g → ℤ} (h : ∀ i, k ∣ v i) (u : Fin g → ℤ) : k ∣ u ⬝ᵥ v :=
  Finset.dvd_sum fun j _ => (h j).mul_left _

theorem phase_dvd {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ)
    (hB : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₁₂ᵀ i j) (hC : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₂₁ᵀ i j)
    (n n' : Fin g → ℤ) :
    (8 : ℤ) ∣ n ⬝ᵥ n' - (γ.toBlocks₁₁ᵀ *ᵥ n + γ.toBlocks₂₁ᵀ *ᵥ n') ⬝ᵥ
      (γ.toBlocks₁₂ᵀ *ᵥ n + γ.toBlocks₂₂ᵀ *ᵥ n') := by
  have e : (γ.toBlocks₁₁ᵀ *ᵥ n) ⬝ᵥ (γ.toBlocks₂₂ᵀ *ᵥ n') =
      n ⬝ᵥ n' + (γ.toBlocks₁₂ᵀ *ᵥ n) ⬝ᵥ (γ.toBlocks₂₁ᵀ *ᵥ n') := by
    rw [mulVec_transpose, mulVec_transpose γ.toBlocks₁₂, ← dotProduct_mulVec, ← dotProduct_mulVec,
      mulVec_mulVec, mulVec_mulVec, sp_rel_int hγ, add_mulVec, one_mulVec, dotProduct_add]
  have d1 := dvd_dot_left (dvd_mulVec hB n) (γ.toBlocks₂₁ᵀ *ᵥ n')
  have d2 := dvd_dot_right (dvd_mulVec hB n) (γ.toBlocks₁₁ᵀ *ᵥ n)
  have d3 := dvd_dot_left (dvd_mulVec hC n') (γ.toBlocks₁₂ᵀ *ᵥ n + γ.toBlocks₂₂ᵀ *ᵥ n')
  rw [add_dotProduct, dotProduct_add, e]
  omega

theorem half_mulVec (M : Matrix (Fin g) (Fin g) ℤ) (N : Matrix (Fin g) (Fin g) ℤ)
    (n n' : Fin g → ℤ) :
    ofRealVec (halfVec (M *ᵥ n + N *ᵥ n')) =
      M.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n) +
        N.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n') := by
  ext i
  simp [ofRealVec, halfVec, Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc, add_div]

theorem theta_zero_shift_sq (a b : Fin g → ℝ) (z : Fin g → ℂ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ.IsSymm) :
    theta (halfVec 0) (halfVec 0) (z + τ *ᵥ ofRealVec a + ofRealVec b) τ ^ 2 =
      eC (2 * (-(ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a)) / 2 - ofRealVec a ⬝ᵥ (z + ofRealVec b))) *
        theta a b z τ ^ 2 := by
  have h0 : halfVec (0 : Fin g → ℤ) = 0 := by ext i; simp [halfVec]
  have h00 : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
  rw [h0, thetaRealTransl_holds (Fin g) 0 0 a b z τ hτ, mul_pow, eC_pow, h00, zero_add, zero_add,
    add_zero]
  norm_num

theorem theta_sq_law_of_zero : ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) → ∀ (c : ℂ) (n n' : Fin g → ℤ), (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec 0) (halfVec 0) (zAct γ τ z) (spAct γ τ) ^ 2 = c * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2) → (∀ i, (2 : ℤ) ∣ (γ.toBlocks₁₁ᵀ *ᵥ n) i - n i) ∧ (∀ i, (2 : ℤ) ∣ (γ.toBlocks₂₂ᵀ *ᵥ n') i - n' i) → (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec n) (halfVec n') (zAct γ τ z) (spAct γ τ) ^ 2 = c * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec n) (halfVec n') z τ ^ 2) := by
  intro g γ hγ h8 c n n' h0 ⟨hn, hn'⟩ τ hτ z
  have hB : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₁₂ᵀ i j := fun i j => (h8 j i).1
  have hC : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₂₁ᵀ i j := fun i j => (h8 j i).2
  have hj := jAut_isUnit hγ hτ
  have hσ := spAct_isSymm hγ hτ.1 hj
  set m := γ.toBlocks₁₁ᵀ *ᵥ n + γ.toBlocks₂₁ᵀ *ᵥ n' with hm
  set m' := γ.toBlocks₁₂ᵀ *ᵥ n + γ.toBlocks₂₂ᵀ *ᵥ n' with hm'
  obtain ⟨k1, k2⟩ := shift_algebra (cMat γ).toBlocks₁₁ (cMat γ).toBlocks₁₂ (cMat γ).toBlocks₂₁
    (cMat γ).toBlocks₂₂ τ (spAct γ τ) (jAut γ τ)⁻¹ hτ.1 hσ (Matrix.nonsing_inv_mul _ hj)
    (Matrix.mul_nonsing_inv _ hj) rfl (sp_A hγ hτ.1 hj) (sp_rel_transpose hγ).2
    (ofRealVec (halfVec n)) (ofRealVec (halfVec n')) z (ofRealVec (halfVec m))
    (ofRealVec (halfVec m')) (half_mulVec _ _ n n') (half_mulVec _ _ n n')
  have h := h0 τ hτ (z + τ *ᵥ ofRealVec (halfVec m) + ofRealVec (halfVec m'))
  have hred : theta (halfVec m) (halfVec m') z τ ^ 2 = theta (halfVec n) (halfVec n') z τ ^ 2 := by
    rw [theta_sq_red m m', theta_sq_red n n']
    have e1 : (fun i => m i % 2) = fun i => n i % 2 := by
      funext i
      have a1 := hn i
      have a2 := dvd_mulVec hC n' i
      simp only [hm, Pi.add_apply]
      omega
    have e2 : (fun i => m' i % 2) = fun i => n' i % 2 := by
      funext i
      have a1 := hn' i
      have a2 := dvd_mulVec hB n i
      simp only [hm', Pi.add_apply]
      omega
    rw [e1, e2]
  obtain ⟨t, ht⟩ := phase_dvd hγ hB hC n n'
  have hph : ofRealVec (halfVec n) ⬝ᵥ ofRealVec (halfVec n') -
      ofRealVec (halfVec m) ⬝ᵥ ofRealVec (halfVec m') = ((2 * t : ℤ) : ℂ) := by
    have ht' : ((n ⬝ᵥ n' : ℤ) : ℂ) - ((m ⬝ᵥ m' : ℤ) : ℂ) = 8 * (t : ℂ) := by exact_mod_cast ht
    simp only [ofRealVec_halfVec, smul_dotProduct, dotProduct_smul, ofIntVec_dot, smul_eq_mul]
    push_cast
    linear_combination (1 / 4 : ℂ) * ht'
  rw [zAct, k1, theta_zero_shift_sq _ _ _ hσ, theta_zero_shift_sq _ _ _ hτ.1, hred, ← mul_assoc,
    mul_assoc (c * _), ← eC_add, expArg, k2, hph, eC_add, eC_add, eC_int, mul_one] at h
  have hne : ∀ x, eC x ≠ 0 := fun x => Complex.exp_ne_zero _
  refine mul_left_cancel₀ (hne _) (h.trans ?_)
  rw [expArg]
  ring

end GlobalTheory.ThetaCharMult
end
end

open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ThetaRatio

theorem thetaChar_ofRealVec {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ)
    (z : Fin g → ℂ) : thetaChar τ (ofRealVec a) (ofRealVec b) z = theta a b z τ := by
  refine tsum_congr fun l => ?_
  have e : ((fun i => (l i : ℂ)) + ofRealVec a) = shiftVec a l := rfl
  rw [e, thetaTerm, eC]
  congr 1
  ring

theorem exists_eq_halfVec {g : ℕ} {c : Fin g → ℂ} (h : ∀ k, c k = 0 ∨ c k = 1 / 2) :
    ∃ n : Fin g → ℤ, c = ofRealVec (halfVec n) := by
  have : ∀ k, ∃ m : ℤ, c k = (((m : ℝ) / 2 : ℝ) : ℂ) := fun k => by
    rcases h k with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose n hn using this
  exact ⟨n, funext hn⟩

theorem ratio_sq_eq_det_jAut : ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) → (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec 0) (halfVec 0) (zAct γ τ z) (spAct γ τ) ^ 2 = 1 * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2) → ∀ (c₁ c₂ : Fin g → ℂ), (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → ∀ τ ∈ SiegelH (Fin g), ∀ (ρ : (Fin g → ℂ) → ℂ) (κ : ℂ), Differentiable ℂ ρ → (∀ z, ρ z ≠ 0) → ρ 0 = 1 → κ ≠ 0 → (∀ z, thetaChar (spAct γ τ) c₁ c₂ (zAct γ τ z) * ρ z = κ * thetaChar τ c₁ c₂ z) → κ ^ 2 = (jAut γ τ).det := by
  intro g γ hγ h8 h0 c₁ c₂ h₁ h₂ τ hτ ρ κ hρ hρ0 hρ1 hκ h
  obtain ⟨n, rfl⟩ := exists_eq_halfVec h₁
  obtain ⟨n', rfl⟩ := exists_eq_halfVec h₂
  simp only [thetaChar_ofRealVec] at h
  have hfix := halfChar_fixed_of_theta_transform_unit g γ hγ h8 1 n n' one_ne_zero h0 τ hτ
    (fun z => κ / ρ z) (by simpa only [div_eq_mul_inv] using (hρ.fun_inv hρ0).const_mul κ) (fun z => div_ne_zero hκ (hρ0 z))
    (fun z => by rw [div_mul_eq_mul_div, ← h z, mul_div_cancel_right₀ _ (hρ0 z)])
  have hlaw := ThetaCharMult.theta_sq_law_of_zero g γ hγ h8 1 n n' h0 hfix τ hτ
  have hE : Differentiable ℂ fun z => eC (expArg γ τ z) := by
    simp only [eC, expArg, dotProduct, mulVec]
    fun_prop
  have hθ : (fun z => theta (halfVec n) (halfVec n') z τ ^ 2) ≠ 0 := fun hz =>
    theta_ne_zero hτ (halfVec n) (halfVec n')
      (funext fun z => pow_eq_zero_iff (two_ne_zero) |>.1 (congrFun hz z))
  have key := entire_eq_zero_of_mul_continuous_eq_zero
    (f := fun z => (jAut γ τ).det * eC (expArg γ τ z) * ρ z ^ 2 - κ ^ 2)
    (((hE.const_mul _).mul (hρ.pow 2)).sub_const _)
    ((differentiable_theta hτ (halfVec n) (halfVec n')).continuous.pow 2) hθ
    (fun z => by
      have h1 := hlaw z
      have h2 : (theta (halfVec n) (halfVec n') (zAct γ τ z) (spAct γ τ) * ρ z) ^ 2 =
          (κ * theta (halfVec n) (halfVec n') z τ) ^ 2 := by rw [h z]
      show _ * theta (halfVec n) (halfVec n') z τ ^ 2 = 0
      linear_combination h2 - ρ z ^ 2 * h1) 0
  have e0 : eC (expArg γ τ 0) = 1 := by simp [expArg, eC]
  simp only [e0, hρ1] at key
  linear_combination -key

end GlobalTheory.ThetaRatio
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeDatumOfSelfDualLattice
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix nonZeroDivisors TensorProduct

namespace GlobalTheory.LatticeDatum

theorem exists_nsmul_mem {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module (𝓞 E) V] [Module E V]
    [IsScalarTower (𝓞 E) E V] (A B : Submodule (𝓞 E) V) (hA : A.FG)
    (hB : Submodule.span E (B : Set V) = ⊤) : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ A, N • x ∈ B := by
  have h1 : ∀ v : V, ∃ N : ℕ, 0 < N ∧ N • v ∈ B := fun v => by
    have hv : v ∈ Submodule.span E (B : Set V) := by rw [hB]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ v hv
    rw [Submodule.span_eq] at ht
    have ht0 : (t : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero t
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {(t : 𝓞 E)}))
    refine ⟨Ideal.absNorm (Ideal.span {(t : 𝓞 E)}), Nat.pos_of_ne_zero ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact ht0
    · rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hs, mul_smul]
      exact B.smul_mem s ht
  obtain ⟨S, rfl⟩ := hA
  choose n hn0 hn using h1
  refine ⟨∏ s ∈ S, n s, Finset.prod_pos fun s _ => hn0 s, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_coe.mp hx)
    rw [hk, mul_comm, mul_smul]
    exact B.toAddSubmonoid.nsmul_mem (hn x) k
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact B.smul_mem c hx

theorem exists_factor {E V L L' : Type} [Field E] [NumberField E] [AddCommGroup V] [Module (𝓞 E) V] [Module E V]
    [IsScalarTower (𝓞 E) E V] [AddCommGroup L] [Module (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L']
    [Module.Finite (𝓞 E) L'] (φ : L →ₗ[𝓞 E] V) (φ' : L' →ₗ[𝓞 E] V) (hφ : Function.Injective φ)
    (hs : Submodule.span E (Set.range φ) = ⊤) :
    ∃ (N : ℕ) (ψ : L' →ₗ[𝓞 E] L), 0 < N ∧ ∀ x, φ (ψ x) = N • φ' x := by
  have hfg : (LinearMap.range φ').FG := by
    rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map φ'
  obtain ⟨N, hN, h⟩ := exists_nsmul_mem (LinearMap.range φ') (LinearMap.range φ) hfg
    (by rw [LinearMap.coe_range]; exact hs)
  choose g hg using fun x : L' => h (φ' x) ⟨x, rfl⟩
  refine ⟨N, ⟨⟨g, fun x y => hφ ?_⟩, fun a x => hφ ?_⟩, hN, hg⟩
  · rw [map_add (f := _), hg, hg, hg, map_add (f := _), smul_add]
  · rw [map_smul, hg, hg, map_smul, smul_comm]; rfl

theorem transport_complexStructure {O L L' : Type} [CommRing O] [AddCommGroup L] [Module O L]
    [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L')
    (ψ : L' →ₗ[O] L) (χ : L →ₗ[O] L') (K c : ℕ) (hK : 0 < K) (hc : 0 < c)
    (h1 : ∀ x, ψ (χ x) = K • x) (h2 : ∀ x, χ (ψ x) = K • x)
    (hB : ∀ x y, B (ψ x) (ψ y) = c * B' x y) (T : O → ℂ)
    (h : ∃ J : ℝ ⊗[ℤ] L →ₗ[ℝ] ℝ ⊗[ℤ] L, (∀ x, J (J x) = -x) ∧
      (∀ x y, B.baseChange ℝ (J x) (J y) = B.baseChange ℝ x y) ∧
      (∀ x, x ≠ 0 → 0 < B.baseChange ℝ (J x) x) ∧
      ∀ (a : O) (A : ℝ ⊗[ℤ] L →ₗ[ℝ] ℝ ⊗[ℤ] L) (t : ℂ), (∀ x : L, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) → t = T a →
        J ∘ₗ A = A ∘ₗ J ∧ LinearMap.trace ℝ _ A = 2 * t.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im) :
    ∃ J : ℝ ⊗[ℤ] L' →ₗ[ℝ] ℝ ⊗[ℤ] L', (∀ x, J (J x) = -x) ∧
      (∀ x y, B'.baseChange ℝ (J x) (J y) = B'.baseChange ℝ x y) ∧
      (∀ x, x ≠ 0 → 0 < B'.baseChange ℝ (J x) x) ∧
      ∀ (a : O) (A : ℝ ⊗[ℤ] L' →ₗ[ℝ] ℝ ⊗[ℤ] L') (t : ℂ), (∀ x : L', A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) → t = T a →
        J ∘ₗ A = A ∘ₗ J ∧ LinearMap.trace ℝ _ A = 2 * t.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im := by
  obtain ⟨J, hJ1, hJ2, hJ3, hJ4⟩ := h
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  let f : ℝ ⊗[ℤ] L' →ₗ[ℝ] ℝ ⊗[ℤ] L := ψ.toAddMonoidHom.toIntLinearMap.baseChange ℝ
  let g : ℝ ⊗[ℤ] L →ₗ[ℝ] ℝ ⊗[ℤ] L' := (K : ℝ)⁻¹ • χ.toAddMonoidHom.toIntLinearMap.baseChange ℝ
  have hf : ∀ (s : ℝ) x, f (s ⊗ₜ x) = s ⊗ₜ ψ x := fun s x => rfl
  have hg : ∀ (s : ℝ) x, g (s ⊗ₜ x) = (K : ℝ)⁻¹ • (s ⊗ₜ χ x) := fun s x => rfl
  have hfg : ∀ x, f (g x) = x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | tmul s x =>
      rw [hg, map_smul, hf, h1, ← TensorProduct.mk_apply, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        inv_mul_cancel₀ hK', one_smul, TensorProduct.mk_apply]
  have hgf : ∀ x, g (f x) = x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | tmul s x =>
      rw [hf, hg, h2, ← TensorProduct.mk_apply, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        inv_mul_cancel₀ hK', one_smul, TensorProduct.mk_apply]
  have hBf : ∀ x y, B.baseChange ℝ (f x) (f y) = c * B'.baseChange ℝ x y := fun x y => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, hx, hx', mul_add]
    | tmul s x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add (f := _), hy, hy', mul_add]
      | tmul u y =>
        rw [hf, hf, LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hB]
        simp only [zsmul_eq_mul]; push_cast; ring
  let e : (ℝ ⊗[ℤ] L') ≃ₗ[ℝ] ℝ ⊗[ℤ] L :=
    LinearEquiv.ofLinear f g (LinearMap.ext hfg) (LinearMap.ext hgf)
  refine ⟨g ∘ₗ J ∘ₗ f, fun x => ?_, fun x y => ?_, fun x hx => ?_, fun a A t hA ht => ?_⟩
  · simp only [LinearMap.comp_apply, hfg, hJ1, map_neg, hgf]
  · apply mul_left_cancel₀ hc'.ne'
    rw [← hBf, ← hBf]
    simp only [LinearMap.comp_apply, hfg, hJ2]
  · have hx' : f x ≠ 0 := fun h0 => hx (by rw [← hgf x, h0, map_zero])
    have := hJ3 _ hx'
    rw [← mul_pos_iff_of_pos_left hc', ← hBf]
    simpa only [LinearMap.comp_apply, hfg] using this
  · obtain ⟨k1, k2, k3⟩ := hJ4 a (f ∘ₗ A ∘ₗ g) t (fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hg, map_smul, hA, ← map_smul χ, ← hg, hfg]) ht
    refine ⟨LinearMap.ext fun x => ?_, ?_, ?_⟩
    · have := congrArg g (LinearMap.congr_fun k1 (f x))
      simpa only [LinearMap.comp_apply, hgf] using this
    · rw [← k2, ← LinearMap.trace_conj' A e]
      congr 1
    · rw [← k3, ← LinearMap.trace_conj' _ e]
      congr 1
      refine LinearMap.ext fun x => ?_
      change f (g (J (f (A (g x))))) = J (f (A (g x)))
      rw [hfg]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp [herm, add_mul, Finset.sum_add_distrib]

noncomputable def traceHerm (ξ : E) (G : Matrix (Fin r) (Fin r) E) : (Fin r → E) →+ (Fin r → E) →+ ℚ :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Algebra.trace ℚ E (ξ * herm G x y))
    fun y y' => by rw [HermModel.herm_add_right, mul_add, map_add (f := _)])
    fun x x' => AddMonoidHom.ext fun y => by
      change Algebra.trace ℚ E (ξ * herm G (x + x') y) =
        Algebra.trace ℚ E (ξ * herm G x y) + Algebra.trace ℚ E (ξ * herm G x' y)
      rw [herm_add_left, mul_add, map_add (f := _)]

theorem exists_datum_of_embedding (H : Host E) (D : Datum H) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (hinj : Function.Injective φ)
    (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hEF : ∀ x y, ((D.EF x y : ℤ) : ℚ) = traceHerm ξ Gm (φ x) (φ y))
    (L : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L]
    (φ' : L →ₗ[𝓞 E] (Fin r → E)) (hinj' : Function.Injective φ')
    (hspan' : Submodule.span E (Set.range φ') = ⊤)
    (hdual : ∀ v, (∀ y, ∃ n : ℤ, traceHerm ξ Gm v (φ' y) = n) ↔ v ∈ LinearMap.range φ') :
    ∃ (D' : Datum H) (φ'' : D'.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p ∧ D'.q = D.q ∧
      LinearMap.range φ'' = LinearMap.range φ' ∧ Function.Injective φ'' ∧
      ∀ x y, ((D'.EF x y : ℤ) : ℚ) = traceHerm ξ Gm (φ'' x) (φ'' y) := by
  haveI := D.fin
  obtain ⟨N, ψ, hN, hψ⟩ := exists_factor φ φ' hinj hspan
  obtain ⟨M, χ, hM, hχ⟩ := exists_factor φ' φ hinj' hspan'
  have h1 : ∀ x, ψ (χ x) = (N * M) • x := fun x => hinj (by rw [hψ, hχ, map_nsmul, mul_smul])
  have h2 : ∀ x, χ (ψ x) = (N * M) • x := fun x => hinj' (by
    rw [hχ, hψ, map_nsmul, mul_comm, mul_smul])
  choose n hn using fun x : L => (hdual (φ' x)).mpr ⟨x, rfl⟩
  have hl : ∀ x x' y, n (x + x') y = n x y + n x' y := fun x x' y => by
    have := hn (x + x') y
    rw [map_add (f := _), map_add (f := _), AddMonoidHom.add_apply, hn, hn] at this
    exact_mod_cast this.symm
  have hr : ∀ x y y', n x (y + y') = n x y + n x y' := fun x y y' => by
    have := hn x (y + y')
    rw [map_add (f := _), map_add (f := _), hn, hn] at this
    exact_mod_cast this.symm
  let B : LinearMap.BilinForm ℤ L :=
    (AddMonoidHom.mk' (fun x => (AddMonoidHom.mk' (n x) (hr x)).toIntLinearMap)
      fun x x' => LinearMap.ext fun y => hl x x' y).toIntLinearMap
  have hB : ∀ x y, ((B x y : ℤ) : ℚ) = traceHerm ξ Gm (φ' x) (φ' y) := fun x y => (hn x y).symm
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hMQ : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hNN : ((N * N : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hN hN).ne'
  have hsc : ∀ x y, D.EF (ψ x) (ψ y) = (N * N : ℕ) * B x y := fun x y => by
    have := hEF (ψ x) (ψ y)
    rw [hψ, hψ, map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply, ← hB, nsmul_eq_mul, nsmul_eq_mul,
      ← mul_assoc] at this
    exact_mod_cast this
  have hmix : ∀ x y, (N : ℤ) * B x (χ y) = M * D.EF (ψ x) y := fun x y => by
    have e1 := hEF (ψ x) y
    have e2 := hB x (χ y)
    rw [hψ, map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul] at e1
    rw [hχ, map_nsmul, nsmul_eq_mul] at e2
    have : (N : ℚ) * (B x (χ y) : ℤ) = M * (D.EF (ψ x) y : ℤ) := by rw [e1, e2]; ring
    exact_mod_cast this
  have hbij : Function.Bijective B := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have h0 : ψ x = 0 := by
        apply D.unimod.1
        ext y
        have := hmix x y
        rw [hx, LinearMap.zero_apply, mul_zero] at this
        have hMZ : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
        rw [(mul_eq_zero.mp this.symm).resolve_left hMZ, map_zero, LinearMap.zero_apply]
      have h3 := hψ x
      rw [h0, map_zero, ← Nat.cast_smul_eq_nsmul ℚ] at h3
      exact hinj' (by rw [map_zero]; exact (smul_eq_zero.mp h3.symm).resolve_left hNQ)
    · intro f
      obtain ⟨x, hx⟩ := D.unimod.2 (f ∘ₗ χ.toAddMonoidHom.toIntLinearMap)
      have hx' : ∀ y, D.EF x y = f (χ y) := fun y => by rw [hx]; rfl
      have hv : ∀ z, traceHerm ξ Gm ((M : ℚ)⁻¹ • φ x) (φ' z) = f z := fun z => by
        have e1 := hEF x (ψ z)
        rw [hx', h2, map_nsmul, hψ, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at e1
        push_cast at e1
        have e2 : traceHerm ξ Gm (φ x) (φ' z) = M * traceHerm ξ Gm ((M : ℚ)⁻¹ • φ x) (φ' z) := by
          rw [← nsmul_eq_mul, ← AddMonoidHom.nsmul_apply, ← map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
            mul_inv_cancel₀ hMQ, one_smul]
        rw [e2, ← mul_assoc] at e1
        exact (mul_left_cancel₀ (mul_ne_zero hNQ hMQ) e1).symm
      obtain ⟨w, hw⟩ := (hdual _).mp fun z => ⟨f z, hv z⟩
      refine ⟨w, LinearMap.ext fun z => ?_⟩
      have := hB w z
      rw [hw, hv] at this
      exact_mod_cast this
  haveI : Module.IsTorsionFree (𝓞 E) L := Function.Injective.moduleIsTorsionFree φ' hinj' (map_smul φ')
  haveI : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  refine ⟨{ La := L, fin := inferInstance, proj := hproj, EF := B, alt := fun x => ?_, unimod := hbij,
            adj := fun a x y => ?_, p := D.p, q := D.q, rank := ?_, dom := ?_ }, φ', rfl, rfl, rfl, hinj', hB⟩
  · apply mul_left_cancel₀ hNN
    rw [← hsc, D.alt, mul_zero]
  · apply mul_left_cancel₀ hNN
    rw [← hsc, ← hsc, map_smul ψ, map_smul ψ, D.adj]
  · rw [← D.rank, HermModel.finrank_eq_of_injective_of_span (K := E) φ hinj hspan,
      HermModel.finrank_eq_of_injective_of_span (K := E) φ' hinj' hspan']
  · exact transport_complexStructure D.EF B ψ χ (N * M) (N * N) (Nat.mul_pos hN hM) (Nat.mul_pos hN hN)
      h1 h2 hsc _ D.dom

theorem exists_datum_of_selfDual (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E))
    (Λ' : Submodule (𝓞 E) (Fin r → E)) (_hξ : cc ξ = -ξ)
    (h : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧
      Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y)))
    (hfg : Λ'.FG) (hspan' : Submodule.span E (Λ' : Set (Fin r → E)) = ⊤)
    (hdual : ∀ v : Fin r → E, (∀ y ∈ Λ', ∃ n : ℤ, Algebra.trace ℚ E (ξ * herm Gm v y) = n) ↔ v ∈ Λ') :
    ∃ (D' : Datum H) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p ∧ D'.q = D.q ∧ LinearMap.range φ' = Λ' ∧
      (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧
        Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) := by
  obtain ⟨hinj, hspan, hG, hdet, hEF⟩ := h
  haveI : Module.Finite (𝓞 E) Λ' := Module.Finite.iff_fg.mpr hfg
  obtain ⟨D', φ', hp, hq, hr, hi, hE⟩ := exists_datum_of_embedding H D ξ Gm φ hinj hspan hEF Λ' Λ'.subtype
    Λ'.injective_subtype (by rw [← LinearMap.coe_range, Submodule.range_subtype]; exact hspan')
    (fun v => by
      rw [Submodule.range_subtype, ← hdual]
      exact ⟨fun h y hy => h ⟨y, hy⟩, fun h y => h y y.2⟩)
  rw [Submodule.range_subtype] at hr
  exact ⟨D', φ', hp, hq, hr, hi, by rw [← LinearMap.coe_range, hr]; exact hspan', hG, hdet, hE⟩

end GlobalTheory.LatticeDatum
end
