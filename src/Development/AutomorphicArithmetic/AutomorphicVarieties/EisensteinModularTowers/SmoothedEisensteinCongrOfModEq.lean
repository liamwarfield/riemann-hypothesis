module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinCongrOfModEq
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem zpow_congr_mod {K : Type} [Field K] {M : ℕ} {ζ : K} (hM : 0 < M) (hζ : ζ ^ M = 1) {a b : ℤ}
    (h : a ≡ b [ZMOD M]) : ζ ^ a = ζ ^ b := by
  obtain ⟨k, hk⟩ := h.dvd
  have hz : ζ ^ (M : ℤ) = 1 := by
    rw [zpow_natCast, hζ]
  have hb : b = a + M * k := by
    omega
  rw [hb, zpow_add₀ (by rintro rfl; simp [zero_pow hM.ne'] at hζ), zpow_mul, hz, one_zpow, mul_one]

private theorem eisF_congr_mod {K : Type} [Field K] [CharZero K] (j : ℕ) {M : ℕ} {ζ : K} (hM : 0 < M) (hζ : ζ ^ M = 1)
    {a₁ b₁ a₂ b₂ : ℤ} (h₁ : a₁ ≡ b₁ [ZMOD M]) (h₂ : a₂ ≡ b₂ [ZMOD M]) (n : ℕ) :
    eisF j M ζ a₁ a₂ n = eisF j M ζ b₁ b₂ n := by
  unfold eisF
  split_ifs
  · unfold const0 frc
    have hd : ((M : ℤ) ∣ a₁ ↔ (M : ℤ) ∣ b₁) := by
      rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero, h₁]
    rw [zpow_congr_mod hM hζ h₂, show a₁ % (M : ℤ) = b₁ % M from h₁]
    simp only [hd]
  · unfold coefPos
    refine Finset.sum_congr rfl fun d _ => ?_
    have hc : ∀ x : ℤ, (x ≡ a₁ [ZMOD M] ↔ x ≡ b₁ [ZMOD M]) :=
      fun x => ⟨fun h => h.trans h₁, fun h => h.trans h₁.symm⟩
    simp only [hc, zpow_congr_mod hM hζ (h₂.mul_right (d : ℤ)),
      zpow_congr_mod hM hζ (h₂.mul_right (d : ℤ)).neg]

theorem UpperTheory.smoothedEisenstein_congr_of_modEq :
    ∀ {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K), 0 < M → ζ ^ M = 1 → ∀ {a₁ b₁ a₂ b₂ : ℤ}, a₁ ≡ b₁ [ZMOD M] → a₂ ≡ b₂ [ZMOD M] → smF c j M ζ a₁ a₂ = smF c j M ζ b₁ b₂ := by
  intro K _ _ c j M ζ hM hζ a₁ b₁ a₂ b₂ h₁ h₂
  funext n
  unfold smF
  rw [eisF_congr_mod j hM hζ h₁ h₂, eisF_congr_mod j hM hζ (h₁.mul_left c) (h₂.mul_left c)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinRootPow
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem UpperTheory.eisenstein_coeff_root_pow {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (β n : ℕ) :
    eisF j M (ζ ^ β) a₁ a₂ n = eisF j M ζ a₁ ((β : ℤ) * a₂) n := by
  have hz : ∀ t : ℤ, (ζ ^ β) ^ t = ζ ^ ((β : ℤ) * t) := fun t => by
    rw [zpow_mul, zpow_natCast]
  unfold eisF const0 coefPos
  simp only [hz, mul_neg, mul_assoc]

theorem UpperTheory.smoothedEisenstein_root_pow :
    ∀ {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (β : ℕ), ζ ≠ 0 → smF c j M (ζ ^ β) a₁ a₂ = smF c j M ζ a₁ ((β : ℤ) * a₂) := by
  intro K _ _ c j M ζ a₁ a₂ β _
  funext n
  unfold smF
  rw [UpperTheory.eisenstein_coeff_root_pow, UpperTheory.eisenstein_coeff_root_pow, mul_left_comm (β : ℤ) c a₂]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.NormalModularTowerTopAlgebraModel
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.normal_modularTowerTop_algebraModel :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ), M ≠ 0 → @Normal (topF X M) (topL X M) _ _ (algMdl X _ _) := by
  intro Ω _ _ _ ε X M hM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hζ := isPrimitiveRoot_eOm ε hM
  have hS : fixMu Ω M = (IntermediateField.adjoin ℚ {eOm ε (1 / (M : ℚ))}).fixingSubgroup := by
    unfold fixMu
    congr 1
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      haveI : NeZero M := ⟨hM⟩
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
      exact pow_mem (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)) i
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.subset_adjoin ℚ _ hζ.pow_eq_one
  have h := GlobalTheory.K4.LevNormal.normal Ω ε X (CongruenceSubgroup.Gamma M) M _ (Nat.pos_of_ne_zero hM) hζ le_rfl
  rw [← hS] at h
  exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.RingHomApplySmoothedEisensteinCoeff
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem UpperTheory.ring_hom_eisenstein_coeff {K : Type} [Field K] [CharZero K] (s : K →+* K) (j M : ℕ) (ζ : K) (a₁ a₂ b₂ : ℤ)
    (h : s (ζ ^ a₂) = ζ ^ b₂) (n : ℕ) : s (eisF j M ζ a₁ a₂ n) = eisF j M ζ a₁ b₂ n := by
  have hz : ∀ k : ℤ, s (ζ ^ (a₂ * k)) = ζ ^ (b₂ * k) := by
    intro k
    rw [zpow_mul, zpow_mul, map_zpow₀, h]
  have hz' : ∀ k : ℤ, s (ζ ^ (-(a₂ * k))) = ζ ^ (-(b₂ * k)) := by
    intro k
    rw [zpow_neg, zpow_neg, map_inv₀, hz]
  unfold eisF const0 coefPos
  split_ifs
  · simp only [map_div₀, map_mul, map_add (f := _), map_sub, map_one, map_ofNat, h]
  · simp only [map_ratCast]
  · simp only [map_neg, map_ratCast]
  · set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_sub]
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    · split_ifs
      · rw [map_mul, map_pow, map_div₀, map_natCast, map_natCast, hz]
      · exact map_zero s
    · split_ifs
      · rw [map_mul, map_pow, map_neg, map_div₀, map_natCast, map_natCast, hz']
      · exact map_zero s

theorem UpperTheory.ringHom_apply_smoothedEisensteinCoeff :
    ∀ {K : Type} [Field K] [CharZero K] (s : K →+* K) (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ b₂ : ℤ), ζ ≠ 0 → s (ζ ^ a₂) = ζ ^ b₂ → ∀ n : ℕ, s (smF c j M ζ a₁ a₂ n) = smF c j M ζ a₁ b₂ n := by
  intro K _ _ s c j M ζ a₁ a₂ b₂ _ h n
  have hc : s (ζ ^ (c * a₂)) = ζ ^ (c * b₂) := by
    rw [mul_comm c a₂, mul_comm c b₂, zpow_mul, zpow_mul, map_zpow₀, h]
  unfold smF
  rw [map_sub, map_mul, map_mul, UpperTheory.ring_hom_eisenstein_coeff s j M ζ a₁ a₂ b₂ h n,
    UpperTheory.ring_hom_eisenstein_coeff s j M ζ (c * a₁) (c * a₂) (c * b₂) hc n]
  simp only [map_pow, map_zpow₀, map_intCast]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinCoeffShiftSecondIndex
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem zpow_cg {K : Type} [Field K] {M : ℕ} {ζ : K} (hM : 0 < M) (hζ : ζ ^ M = 1) {x y : ℤ}
    (h : x ≡ y [ZMOD M]) : ζ ^ x = ζ ^ y := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  obtain ⟨k, hk⟩ := h.dvd
  have : y = x + (M : ℤ) * k := by linarith
  rw [this, zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

private theorem eisF_shift {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (a₁ a₂ e : ℤ) (hM : 0 < M)
    (hζ : ζ ^ M = 1) (n : ℕ) :
    eisF j M ζ a₁ (a₂ + e * a₁) n = ζ ^ (e * (n : ℤ)) * eisF j M ζ a₁ a₂ n := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  unfold eisF
  split_ifs with hn
  · subst hn
    simp only [Nat.cast_zero, mul_zero, zpow_zero, one_mul]
    unfold const0
    by_cases hd : (M : ℤ) ∣ a₁
    · have : ζ ^ (a₂ + e * a₁) = ζ ^ a₂ :=
        zpow_cg hM hζ (Int.ModEq.symm ((Int.modEq_iff_dvd).2 (by simpa using hd.mul_left e)))
      rw [this]
    · simp only [if_neg hd]
  · unfold coefPos
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hnd : (n : ℤ) = ((n / d : ℕ) : ℤ) * d := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
    rw [mul_sub]
    congr 1
    · split_ifs with h
      · have : ζ ^ ((a₂ + e * a₁) * d) = ζ ^ (e * (n : ℤ)) * ζ ^ (a₂ * d) := by
          rw [← zpow_add₀ h0]
          apply zpow_cg hM hζ
          have h2 := ((h.symm.mul_left e).add_left a₂).mul_right (d : ℤ)
          refine h2.trans ?_
          rw [show (a₂ + e * ((n / d : ℕ) : ℤ)) * d = e * (((n / d : ℕ) : ℤ) * d) + a₂ * d by ring, ← hnd]
        rw [this]; ring
      · rw [mul_zero]
    · split_ifs with h
      · have : ζ ^ (-((a₂ + e * a₁) * d)) = ζ ^ (e * (n : ℤ)) * ζ ^ (-(a₂ * d)) := by
          rw [← zpow_add₀ h0]
          apply zpow_cg hM hζ
          have h2 := (((h.symm.mul_left e).add_left a₂).mul_right (d : ℤ)).neg
          refine h2.trans ?_
          rw [show -((a₂ + e * -((n / d : ℕ) : ℤ)) * d) = e * (((n / d : ℕ) : ℤ) * d) + -(a₂ * d) by ring, ← hnd]
        rw [this]; ring
      · rw [mul_zero]

theorem UpperTheory.smoothedEisensteinCoeff_shift_second_index :
    ∀ {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ e : ℤ), 0 < M → ζ ^ M = 1 → ∀ n : ℕ, smF c j M ζ a₁ (a₂ + e * a₁) n = ζ ^ (e * (n : ℤ)) * smF c j M ζ a₁ a₂ n := by
  intro K _ _ c j M ζ a₁ a₂ e hM hζ n
  unfold smF
  rw [show c * (a₂ + e * a₁) = c * a₂ + e * (c * a₁) by ring, eisF_shift j M ζ a₁ a₂ e hM hζ,
    eisF_shift j M ζ (c * a₁) (c * a₂) e hM hζ]
  ring
end
