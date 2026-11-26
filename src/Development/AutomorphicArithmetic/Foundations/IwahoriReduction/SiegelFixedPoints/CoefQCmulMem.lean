module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.ConstInt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitEdgeClassKummerDlogCongruence

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.DvdOfModEq
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L

section Series

variable {K : Type} [Field K] [CharZero K]

end Series

section Root

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω]

end Root

end UpperTheory.Kd.L

private theorem eps_eOm_eq_cexp {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * ↑Real.pi * Complex.I * ↑x) := by
  unfold eOm
  apply Function.invFun_eq
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero ((x.den : ℕ) : Ω) := ⟨by exact_mod_cast x.den_nz⟩
  haveI : NeZero x.den := ⟨x.den_nz⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω x.den
  have h2 := hξ.map_of_injective ε.injective
  have h1 : Complex.exp (2 * ↑Real.pi * Complex.I * ↑x) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have hx : (x : ℂ) * (x.den : ℂ) = (x.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num x
    linear_combination (2 * ↑Real.pi * Complex.I) * hx
  obtain ⟨i, -, hi⟩ := h2.eq_pow_of_pow_eq_one h1
  exact ⟨ξ ^ i, by rw [map_pow, hi]⟩

private theorem eOm_inv_mul_pow_eq_eOm_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (D M : ℕ) (hD : 0 < D) :
    eOm ε (1 / ((D * M : ℕ) : ℚ)) ^ D = eOm ε (1 / (M : ℚ)) := by
  apply ε.injective
  rw [map_pow, eps_eOm_eq_cexp, eps_eOm_eq_cexp, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  have : (D:ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  by_cases hM : (M:ℂ) = 0
  · simp [hM]
  · field_simp

private theorem eisF_mul_scale_eq_ite_dvd {K : Type*} [Field K] (D M : ℕ) (ζ' ζ : K) (hζ : ζ' ^ D = ζ) (A a : ℤ) (hD : 0 < D) (hA : ¬ (M:ℤ) ∣ A) (n : ℕ) :
    eisF 1 (D * M) ζ' ((D:ℤ) * A) ((D:ℤ) * a) n = if D ∣ n then eisF 1 M ζ A a (n / D) else 0 := by
  have hD' : (D:ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have key : ∀ x : ℤ, x ≡ (D:ℤ) * A [ZMOD ((D * M : ℕ) : ℤ)] → (D:ℤ) ∣ x := by
    intro x hx
    have h := hx.symm.dvd
    push_cast at h
    have h2 : (D:ℤ) ∣ x - D * A := (Dvd.intro _ rfl).trans h
    have h3 : (D:ℤ) ∣ D * A := Dvd.intro _ rfl
    simpa using h2.add h3
  have cong : ∀ y : ℤ, (((D:ℤ) * y) ≡ (D:ℤ) * A [ZMOD ((D * M : ℕ) : ℤ)] ↔ y ≡ A [ZMOD M]) := by
    intro y
    push_cast
    exact ⟨Int.ModEq.mul_left_cancel' hD', fun h => Int.ModEq.mul_left' h⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [eisF, const0, if_true, dvd_zero, Nat.zero_div]
    have h1 : ¬ ((D * M : ℕ) : ℤ) ∣ (D:ℤ) * A := by
      push_cast
      rwa [mul_dvd_mul_iff_left hD']
    rw [if_neg h1, if_neg hA]
    unfold frc
    push_cast
    rw [Int.mul_emod_mul_of_pos _ _ (by exact_mod_cast hD)]
    push_cast
    have : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp
  · simp only [eisF, coefPos, hn.ne', if_false, Nat.sub_self, pow_zero, one_mul]
    by_cases hDn : D ∣ n
    · rw [if_pos hDn]
      obtain ⟨k, rfl⟩ := hDn
      have hk : k ≠ 0 := by
        rintro rfl
        simp at hn
      rw [Nat.mul_div_cancel_left k hD, if_neg hk]
      have hsub : k.divisors ⊆ (D * k).divisors :=
        Nat.divisors_subset_of_dvd (Nat.mul_ne_zero hD.ne' hk) (dvd_mul_left k D)
      have hpow : ∀ t : ℤ, ζ' ^ ((D:ℤ) * t) = ζ ^ t := by
        intro t
        rw [zpow_mul, zpow_natCast, hζ]
      have hout : ∀ x : ℕ, x ∣ D * k → (D:ℤ) ∣ ((D * k / x : ℕ) : ℤ) → x ∣ k := by
        intro x hx hdx
        rw [Int.natCast_dvd_natCast] at hdx
        obtain ⟨e, he⟩ := hdx
        have h1 : D * k / x * x = D * k := Nat.div_mul_cancel hx
        rw [he, mul_assoc] at h1
        exact ⟨e, by rw [mul_comm x e]; exact (Nat.eq_of_mul_eq_mul_left hD h1).symm⟩
      rw [← Finset.sum_subset hsub]
      · apply Finset.sum_congr rfl
        intro x hx
        have hxk : x ∣ k := Nat.dvd_of_mem_divisors hx
        have e1 : ((D * k / x : ℕ) : ℤ) = (D:ℤ) * ((k / x : ℕ) : ℤ) := by
          rw [Nat.mul_div_assoc D hxk]
          push_cast
          ring
        simp only [e1, neg_mul_eq_mul_neg, cong, mul_assoc, hpow]
      · intro x hx hxn
        have hx' : x ∣ D * k := Nat.dvd_of_mem_divisors hx
        have hnot : ¬ x ∣ k := fun h => hxn (Nat.mem_divisors.mpr ⟨h, hk⟩)
        rw [if_neg, if_neg, sub_zero]
        · intro h
          exact hnot (hout x hx' (by simpa using key _ h))
        · intro h
          exact hnot (hout x hx' (key _ h))
    · rw [if_neg hDn]
      apply Finset.sum_eq_zero
      intro x hx
      have hx' : x ∣ n := Nat.dvd_of_mem_divisors hx
      have hout : (D:ℤ) ∣ ((n / x : ℕ) : ℤ) → False := by
        intro hdx
        rw [Int.natCast_dvd_natCast] at hdx
        exact hDn (hdx.trans (Nat.div_dvd_of_dvd hx'))
      rw [if_neg, if_neg, sub_zero]
      · intro h
        exact hout (by simpa using key _ h)
      · intro h
        exact hout (key _ h)

private theorem smF_mul_scale_eq_ite_dvd {K : Type*} [Field K] (c : ℤ) (D M : ℕ) (ζ' ζ : K) (hζ : ζ' ^ D = ζ) (A a : ℤ) (hD : 0 < D) (hA : ¬ (M:ℤ) ∣ A) (hcA : ¬ (M:ℤ) ∣ c * A) (n : ℕ) :
    smF c 1 (D * M) ζ' ((D:ℤ) * A) ((D:ℤ) * a) n = if D ∣ n then smF c 1 M ζ A a (n / D) else 0 := by
  unfold smF
  rw [mul_left_comm c (D:ℤ) A, mul_left_comm c (D:ℤ) a, eisF_mul_scale_eq_ite_dvd D M ζ' ζ hζ A a hD hA, eisF_mul_scale_eq_ite_dvd D M ζ' ζ hζ (c * A) (c * a) hD hcA]
  split_ifs <;> simp

private theorem cmul_dilate_eq_ite_dvd {K : Type*} [Field K] (D : ℕ) (hD : 0 < D) (f g f' g' : ℕ → K) (hf : ∀ n, f' n = if D ∣ n then f (n / D) else 0) (hg : ∀ n, g' n = if D ∣ n then g (n / D) else 0) (N : ℕ) :
    cmul f' g' N = if D ∣ N then cmul f g (N / D) else 0 := by
  unfold cmul
  by_cases hN : D ∣ N
  · rw [if_pos hN]
    obtain ⟨K0, rfl⟩ := hN
    rw [Nat.mul_div_cancel_left K0 hD]
    have hsub : (Finset.range (K0 + 1)).image (fun k => D * k) ⊆ Finset.range (D * K0 + 1) := by
      intro i hi
      simp only [Finset.mem_image, Finset.mem_range] at hi ⊢
      obtain ⟨k, hk, rfl⟩ := hi
      have := Nat.mul_le_mul_left D (Nat.lt_succ_iff.mp hk)
      omega
    rw [← Finset.sum_subset hsub, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro k hk
      have e : D * K0 - D * k = D * (K0 - k) := (Nat.mul_sub D K0 k).symm
      rw [hf, hg, if_pos (dvd_mul_right D k), e, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hD, Nat.mul_div_cancel_left _ hD]
    · intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left hD hxy
    · intro i hi hni
      rw [hf]
      split_ifs with hDi
      · exfalso
        obtain ⟨k, rfl⟩ := hDi
        apply hni
        simp only [Finset.mem_image, Finset.mem_range] at hi ⊢
        refine ⟨k, ?_, rfl⟩
        have h1 : D * k ≤ D * K0 := by omega
        have := Nat.le_of_mul_le_mul_left h1 hD
        omega
      · simp
  · rw [if_neg hN]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hf, hg]
    split_ifs with h1 h2
    · exfalso
      apply hN
      have := Nat.dvd_add h1 h2
      rwa [Nat.add_sub_cancel' hi'] at this
    · simp
    · simp
    · simp

private theorem coefQ_eq_of_mul_eq_nat {Ω : Type} [Field Ω] (L : ℕ) (hL : 0 < L) (F : ℕ → Ω) (r : ℚ) (N : ℕ) (h : r * L = N) :
    coefQ L F r = F N := by
  unfold coefQ
  have hL' : (0:ℚ) < L := by exact_mod_cast hL
  have hr : 0 ≤ r := by
    have h0 : 0 ≤ r * L := by
      rw [h]
      exact Nat.cast_nonneg _
    exact (mul_nonneg_iff_of_pos_right hL').mp h0
  rw [if_pos ⟨hr, by rw [h]; simp⟩, h]
  simp

private theorem coefQ_eq_zero_of_not_nat {Ω : Type} [Field Ω] (L : ℕ) (F : ℕ → Ω) (r : ℚ) (h : ¬ ∃ N : ℕ, r * L = N) :
    coefQ L F r = 0 := by
  unfold coefQ
  rw [if_neg]
  rintro ⟨hr, hd⟩
  apply h
  have h1 : ((r * L).num : ℚ) = r * L := Rat.coe_int_num_of_den_eq_one hd
  have h2 : 0 ≤ (r * L).num := Rat.num_nonneg.mpr (mul_nonneg hr (Nat.cast_nonneg _))
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h2
  refine ⟨m, ?_⟩
  rw [← h1, hm]
  simp

theorem UpperTheory.Kd.L.resc :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (D M c d L : ℕ) (A a B b : ℤ), 0 < D → 0 < M → 0 < L → ¬ (M : ℤ) ∣ A → ¬ (M : ℤ) ∣ c * A → ¬ (M : ℤ) ∣ B → ¬ (M : ℤ) ∣ d * B → ∀ r : ℚ, coefQ L (cmul (smF c 1 (D * M) (eOm ε (1 / ((D * M : ℕ) : ℚ))) (D * A) (D * a)) (smF d 1 (D * M) (eOm ε (1 / ((D * M : ℕ) : ℚ))) (D * B) (D * b))) r = coefQ L (cmul (smF c 1 M (eOm ε (1 / (M : ℚ))) A a) (smF d 1 M (eOm ε (1 / (M : ℚ))) B b)) (r / D) := by
  intro Ω _ _ _ _ ε D M c d L A a B b hD hM hL hA hcA hB hdB r
  have hζ := eOm_inv_mul_pow_eq_eOm_inv ε D M hD
  have h1 := smF_mul_scale_eq_ite_dvd (c:ℤ) D M _ _ hζ A a hD hA hcA
  have h2 := smF_mul_scale_eq_ite_dvd (d:ℤ) D M _ _ hζ B b hD hB hdB
  have hc := cmul_dilate_eq_ite_dvd D hD _ _ _ _ h1 h2
  by_cases h : ∃ N : ℕ, r * L = N
  · obtain ⟨N, hN⟩ := h
    rw [coefQ_eq_of_mul_eq_nat L hL _ r N hN, hc]
    by_cases hDN : D ∣ N
    · obtain ⟨K0, rfl⟩ := hDN
      rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hD]
      refine (coefQ_eq_of_mul_eq_nat L hL _ _ K0 ?_).symm
      have hD' : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
      rw [div_mul_eq_mul_div, hN]
      push_cast
      field_simp
    · rw [if_neg hDN, coefQ_eq_zero_of_not_nat]
      rintro ⟨m, hm⟩
      apply hDN
      refine ⟨m, ?_⟩
      have hD' : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
      have e : (N:ℚ) = D * m := by
        rw [← hN, ← hm]
        field_simp
      exact_mod_cast e
  · rw [coefQ_eq_zero_of_not_nat L _ r h, coefQ_eq_zero_of_not_nat]
    rintro ⟨m, hm⟩
    apply h
    refine ⟨D * m, ?_⟩
    have hD' : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    push_cast
    rw [← hm]
    field_simp
end

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L.One

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem eOm_zero' : eOm ε 0 = 1 := by
  have h : Function.invFun ε (ε 1) = 1 := Function.leftInverse_invFun ε.injective 1
  simpa [eOm] using h

private theorem gal_sl_g [IsAlgClosed Ω] (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) {s : Ω ≃ₐ[ℚ] Ω} (hs : s ∈ fixMu Ω M)
    (g : SL(2, ℤ)) {f : X.K} (hf : f ∈ topL X M) : X.gal s (X.sl (ofSL g) f) = X.sl (ofSL g) (X.gal s f) := by
  rw [mem_lev_iff] at hf
  have hζ := isPrimitiveRoot_eOm ε hM
  exact X.recip M f (Nat.pos_of_ne_zero hM) hf _ hζ s 1
    (by rw [zpow_one]; exact (mem_fixMu_iff s).1 hs _ hζ.pow_eq_one) g g (by simp)

private theorem coe_diag {D : ℕ} (hD : 0 < D) :
    (((toGQ !![(D : ℤ), 0; 0, 1] : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(D : ℚ), 0; 0, 1] := by
  have h : (0 : ℤ) < (!![(D : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; exact_mod_cast hD
  rw [toGQ, dite_eq_left h]
  show (!![(D : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem coe_T (k : ℕ) :
    (((ofSL (ModularGroup.T ^ k) : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, (k : ℚ); 0, 1] := by
  have he : ((ModularGroup.T ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (k : ℤ); 0, 1] := by
    rw [← ModularGroup.coe_T_zpow, zpow_natCast]
  show ((ModularGroup.T ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) = _
  rw [he]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem ent_diag {D : ℕ} (hD : 0 < D) (i j : Fin 2) :
    ent (toGQ !![(D : ℤ), 0; 0, 1]) i j = (!![(D : ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) i j := by
  rw [ent, coe_diag hD]

private theorem gal_sl_diag (X : Tower Ω ε) {D : ℕ} (hD : 0 < D) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal s (X.sl (toGQ !![(D : ℤ), 0; 0, 1]) f) = X.sl (toGQ !![(D : ℤ), 0; 0, 1]) (X.gal s f) := by
  apply exp_injective X
  ext r
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have key : ∀ (h : X.K), (X.exp (X.sl (toGQ !![(D : ℤ), 0; 0, 1]) h)).coeff r = (X.exp h).coeff (r / D) := by
    intro h
    have := X.exp_upper (toGQ !![(D : ℤ), 0; 0, 1]) (by rw [ent_diag hD]; simp) h (r / D)
    simp only [ent_diag hD] at this
    simp at this
    rw [div_mul_cancel₀ _ hD', eOm_zero', one_mul] at this
    exact this
  rw [X.gal_exp, key, key, X.gal_exp]

private theorem rescale_series (φ : HahnSeries ℚ Ω) {D : ℚ} (hD : 0 < D) :
    ∃ φ' : HahnSeries ℚ Ω, ∀ r : ℚ, φ'.coeff r = φ.coeff (r / D) := by
  refine ⟨⟨fun r => φ.coeff (r / D), ?_⟩, fun r => rfl⟩
  have h := φ.isPWO_support.image_of_monotone (f := fun r : ℚ => r * D)
    (fun a b hab => mul_le_mul_of_nonneg_right hab hD.le)
  refine h.mono ?_
  intro r hr
  exact ⟨r / D, hr, div_mul_cancel₀ _ hD.ne'⟩

private theorem diag_mul_T_pow_eq_T_pow_mul_mul_diag (D L : ℕ) (hD : 0 < D) :
    toGQ !![(D : ℤ), 0; 0, 1] * ofSL (ModularGroup.T ^ L) = ofSL (ModularGroup.T ^ (D * L)) * toGQ !![(D : ℤ), 0; 0, 1] := by
  apply Subtype.ext
  apply Units.ext
  show (((toGQ !![(D : ℤ), 0; 0, 1] : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
      (((ofSL (ModularGroup.T ^ L) : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
    (((ofSL (ModularGroup.T ^ (D * L)) : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
      (((toGQ !![(D : ℤ), 0; 0, 1] : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
  rw [coe_diag hD, coe_T, coe_T]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem T_mem_Gamma (M : ℕ) : (ModularGroup.T ^ M : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M := by
  have he : ((ModularGroup.T ^ M : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (M : ℤ); 0, 1] := by
    rw [← ModularGroup.coe_T_zpow, zpow_natCast]
  rw [CongruenceSubgroup.Gamma_mem]
  simp [he]

private theorem e_mem_KT (X : Tower Ω ε) {D L : ℕ} (hD : 0 < D) (g : SL(2, ℤ)) {y : X.K} (hy : y ∈ topL X (L * D)) :
    X.sl (toGQ !![(D : ℤ), 0; 0, 1]) (X.sl (ofSL g) y) ∈ KT X L := by
  rw [KT.mem_def]
  rw [mem_lev_iff] at hy
  have hn : g * ModularGroup.T ^ (D * L) * g⁻¹ ∈ CongruenceSubgroup.Gamma (L * D) := by
    have := (CongruenceSubgroup.Gamma_normal (L * D)).conj_mem _ (T_mem_Gamma (L * D)) g
    rwa [mul_comm L D] at this ⊢
  have h1 := hy _ hn
  simp only [← X.sl_mul]
  rw [mul_assoc, diag_mul_T_pow_eq_T_pow_mul_mul_diag D L hD, ← mul_assoc]
  have e : ofSL g * ofSL (ModularGroup.T ^ (D * L)) = ofSL (g * ModularGroup.T ^ (D * L) * g⁻¹) * ofSL g := by
    simp [map_mul]
  rw [e, mul_assoc, X.sl_mul, h1]

end UpperTheory.Kd.L.One

namespace UpperTheory.Kd.L.One

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem root_mem (A : ValuationSubring Ω) {ζ : Ω} {k : ℕ} (hk : k ≠ 0) (h : ζ ^ k = 1) : ζ ∈ A := by
  have hz : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hk] at h
    exact zero_ne_one h
  rcases A.mem_or_inv_mem ζ with h1 | h1
  · exact h1
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have : ζ = (ζ⁻¹) ^ j := by
      rw [inv_pow]
      rw [pow_succ] at h
      exact eq_inv_of_mul_eq_one_right h
    rw [this]
    exact pow_mem h1 j

private theorem smF_mem [IsAlgClosed Ω] [CharZero Ω] (A : ValuationSubring Ω) {c M : ℕ} (hM : 0 < M) (hc : Nat.Coprime c M) {a : ℤ} (b : ℤ)
    (h : ¬ (M : ℤ) ∣ a) (k : ℕ) : smF (c : ℤ) 1 M (eOm ε (1 / (M : ℚ))) a b k ∈ A := by
  have hζ := isPrimitiveRoot_eOm ε hM.ne'
  have hz : ∀ e : ℤ, eOm ε (1 / (M : ℚ)) ^ e ∈ A := fun e => by
    refine root_mem A hM.ne' ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
  exact GlobalTheory.T.smoothedEisensteinFxCoefficientSeq_one_mem_subring Ω A.toSubring c M _ a b hM hc h (hz b) (hz (-b)) k

private theorem not_dvd_of {l M : ℕ} {a : ℤ} (h : l ∣ M) (ha : ¬ (l : ℤ) ∣ a) : ¬ (M : ℤ) ∣ a :=
  fun h1 => ha ((Int.natCast_dvd_natCast.2 h).trans h1)

private theorem coefQ_cmul_mem (A : ValuationSubring Ω) {f g : ℕ → Ω} (hf : ∀ k, f k ∈ A) (hg : ∀ k, g k ∈ A) (L : ℕ) (r : ℚ) :
    coefQ L (cmul f g) r ∈ A := by
  unfold coefQ
  split_ifs
  · exact sum_mem fun i _ => mul_mem (hf _) (hg _)
  · exact zero_mem _

private theorem zt_pow [IsAlgClosed Ω] (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (k : ℕ) : IsPrimitiveRoot (zt ε l k) (l ^ k) := by
  have h := isPrimitiveRoot_eOm ε (pow_ne_zero k hl)
  rw [Nat.cast_pow] at h
  exact h

end UpperTheory.Kd.L.One

open UpperTheory.Kd.L.One

attribute [local instance] algMdl in
set_option maxHeartbeats 2000000 in
theorem UpperTheory.Kd.L.one :
    ∀ (l : ℕ) [Fact l.Prime], ∃ cc : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (x : ZMod N) (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ g ∈ CongruenceSubgroup.Gamma0 N, ¬ (l : ℤ) ∣ en g 0 0 → ¬ (l : ℤ) ∣ en g 1 0 → (∀ r, EE ε l (m + n) N x c d g r ∈ A) ∧ ∃ ξ : ℚ → Ω, (∀ r, ξ r ∈ A) ∧ ∀ s ∈ fixMu Ω (topMu l n m N), Stab A s → ∀ t : ZMod (l ^ n), s (zt ε l (m + n + n)) = zt ε l n ^ t.val * zt ε l (m + n + n) → ∀ φ : HahnSeries ℚ Ω, IsDl X A l n ((topMu l n m N) : ℚ) (X.sl (ofSL g) (wkMu X l n m N x c d s)) φ → ∀ r : ℚ, CgA A l n ((l : Ω) ^ cc * φ.coeff r) (s (ξ r) - ξ r + (l : Ω) ^ cc * ((N : Ω) ^ 3 * EE ε l (m + n) N x c d g r * (t.val : Ω))) := by
  intro l _
  by_cases h2 : l = 2
  · exact ⟨0, fun ε X N _ c d gm hP => absurd h2 hP.odd⟩
  obtain ⟨cc, hcc⟩ := GlobalTheory.T.siegelUnit_edgeClass_kummer_dlog_congruence l h2
  refine ⟨cc, ?_⟩
  intro Ω _ _ _ _ ε X N _ c d gm hP A hA x m n hm hn g hg hg0 hg1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hlp : l.Prime := Fact.out
  have hl0 : l ≠ 0 := hlp.ne_zero
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hlp
  have hlN : ¬ (l : ℤ) ∣ (N : ℤ) := fun h => hP.cop (Int.natCast_dvd_natCast.1 h)
  have hnd : ∀ e : ℕ, Nat.Coprime e (6 * l * N) → ¬ (l : ℤ) ∣ (e : ℤ) := fun e he h => by
    have h1 : l ∣ Nat.gcd e (6 * l * N) := Nat.dvd_gcd (Int.natCast_dvd_natCast.1 h) (dvd_mul_of_dvd_left (dvd_mul_left l 6) N)
    rw [he] at h1
    exact hlp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hL0 : m + n ≠ 0 := by omega
  have hlL : (l : ℤ) ∣ (l : ℤ) ^ (m + n) := dvd_pow_self _ hL0
  set w1 : ℤ := (N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n) with hw1
  set w2 : ℤ := en g 0 0 * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n) + en g 1 0 with hw2
  have hA1 : ¬ (l : ℤ) ∣ en g 0 0 * w1 := by
    intro h
    rcases hlZ.dvd_or_dvd h with h | h
    · exact hg0 h
    · exact hlN ((dvd_add_left (hlL.mul_left _)).1 h)
  have hB1 : ¬ (l : ℤ) ∣ w2 := fun h => hg1 ((dvd_add_right (hlL.mul_left _)).1 h)
  have hMl : l ∣ N * l ^ (m + n) := (dvd_pow_self l hL0).mul_left N
  have hM0 : 0 < N * l ^ (m + n) := Nat.mul_pos hN0 (pow_pos hlp.pos _)
  have hcop : ∀ e : ℕ, Nat.Coprime e (6 * l * N) → Nat.Coprime e (N * l ^ (m + n)) := fun e he =>
    Nat.Coprime.mul_right (he.coprime_dvd_right (dvd_mul_left _ _))
      (Nat.Coprime.pow_right _ (he.coprime_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left l 6) N)))
  have hEE : ∀ r, EE ε l (m + n) N x c d g r ∈ A := fun r =>
    coefQ_cmul_mem A (fun k => smF_mem A hM0 (hcop c hP.cc) _ (not_dvd_of hMl hA1) k)
      (fun k => smF_mem A hM0 (hcop d hP.dc) _ (not_dvd_of hMl hB1) k) _ r
  refine ⟨hEE, ?_⟩
  obtain ⟨⟨huF, hu0, hvF, hv0⟩, hun⟩ := units ε X l N c d gm hP x m n hm
  obtain ⟨hu1, hu2⟩ := hun g hg
  obtain ⟨hη, hW⟩ := topex ε X l N c d gm hP x m n hm
  have hMM : topMu l n m N ≠ 0 := NeZero.ne _
  have hlM : l ^ n ∣ topMu l n m N := (pow_dvd_pow l (Nat.le_add_left n m)).mul_right _
  have hco : ∀ e : ℕ, Nat.Coprime e (6 * l * N) → Nat.Coprime e (6 * N ^ 3 * l) := fun e he =>
    Nat.Coprime.mul_right (Nat.Coprime.mul_right (he.coprime_dvd_right (dvd_mul_of_dvd_left (dvd_mul_right 6 l) N))
      (Nat.Coprime.pow_right 3 (he.coprime_dvd_right (dvd_mul_left N _))))
      (he.coprime_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left l 6) N))
  have hN2 : ∀ a : ℤ, ¬ (l : ℤ) ∣ a → ¬ (l : ℤ) ∣ (N : ℤ) ^ 2 * a := fun a ha h => by
    rcases hlZ.dvd_or_dvd h with h | h
    · exact hlN (hlZ.dvd_of_dvd_pow h)
    · exact ha h
  have hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := by
    obtain ⟨φ, h1, h2⟩ := X.j_hol
    exact ⟨φ, h2, h1⟩
  haveI hnorm : Normal (topF X (topMu l n m N)) (topL X (topMu l n m N)) := UpperTheory.normal_modularTowerTop_algebraModel X _ hMM
  let e : topL X (topMu l n m N) →+* X.K :=
    ((X.sl (toGQ !![((N * N : ℕ) : ℤ), 0; 0, 1]) : X.K →+* X.K).comp (X.sl (ofSL g) : X.K →+* X.K)).comp
      (topL X (topMu l n m N)).subtype
  have he : ∀ y, e y = X.sl (toGQ !![((N * N : ℕ) : ℤ), 0; 0, 1]) (X.sl (ofSL g) (y : X.K)) := fun _ => rfl
  have hNN : 0 < N * N := Nat.mul_pos hN0 hN0
  have heT : ∀ y, e y ∈ KT X (l ^ (m + n)) := fun y => e_mem_KT X hNN g y.2
  obtain ⟨ξ, hξ, hmain⟩ := hcc ε X hj A hA (m + n) n (N ^ 3) c d
    ((N : ℤ) ^ 2 * (en g 0 0 * w1)) ((N : ℤ) ^ 2 * ((N : ℤ) ^ 2 * en g 0 1)) ((N : ℤ) * en g 0 1)
    ((N : ℤ) ^ 2 * w2) ((N : ℤ) ^ 2 * ((N : ℤ) * en g 1 1)) (en g 1 1)
    (by push_cast; ring_nf; rfl) (by push_cast; ring_nf; rfl)
    (by push_cast; exact ⟨(N : ℤ) * en g 0 1, by ring⟩) (by push_cast; exact ⟨en g 1 1, by ring⟩)
    hn (by omega) (pow_pos hN0 3) (Nat.Coprime.pow_left 3 (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hlp).2 hP.cop)))
    hP.c1 (hco c hP.cc) hP.d1 (hco d hP.dc)
    (not_dvd_of (l := l) ((dvd_pow_self l hL0).mul_left _) (hN2 _ hA1))
    (not_dvd_of (l := l) ((dvd_pow_self l hL0).mul_left _) (hN2 _ hB1))
    (topF X (topMu l n m N)) (topL X (topMu l n m N)) (topBar X (topMu l n m N)) e heT
    (levConst X _ (zt ε l n))
    ⟨_, mdl_le_lev X _ _ huF⟩ ⟨_, mdl_le_lev X _ _ hvF⟩
    (topZeta X (topMu l n m N) l n)
    (topRoot X (topMu l n m N) (l ^ n) (sgN X c N (N * l ^ (m + n)) (w1, 0)))
    (topRoot X (topMu l n m N) (l ^ n) (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ))))
    (by rw [he]; show X.sl _ (X.sl _ (algebraMap Ω X.K (zt ε l n))) = _; rw [AlgEquiv.commutes, AlgEquiv.commutes]) rfl hu1 hu2
    (topRoot_pow X _ (pow_ne_zero n hl0) _) (topRoot_pow X _ (pow_ne_zero n hl0) _)
    (topChar X (topMu l n m N) l n (sgN X c N (N * l ^ (m + n)) (w1, 0)))
    (topChar X (topMu l n m N) l n (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ))))
    (topChar_apply X hl0 hlM huF hu0) (topChar_apply X hl0 hlM hvF hv0)
    _ hη.1 hη.2.1
  have hD0 : (0 : ℚ) < ((N * N : ℕ) : ℚ) := by exact_mod_cast hNN
  refine ⟨fun r => ξ (r * ((N * N : ℕ) : ℚ)), fun r => hξ _, ?_⟩
  intro s hs hSt t ht φ hφ r
  have hsi : s⁻¹ ∈ fixMu Ω (topMu l n m N) := inv_mem hs
  obtain ⟨φ', hφ'⟩ := rescale_series φ hD0
  have hdl := (GlobalTheory.T.isLogDerivQExpansionModPrimePow_rescale ε X hj l A hA n (N * N) _ _ φ φ' hNN hφ').1 hφ
  have hq : (((topMu l n m N : ℕ) : ℚ)) / ((N * N : ℕ) : ℚ) = (l : ℚ) ^ (m + n) := by
    have : ((N * N : ℕ) : ℚ) ≠ 0 := hD0.ne'
    rw [topMu, Nat.cast_mul, mul_div_assoc, div_self this, mul_one, Nat.cast_pow]
  rw [hq] at hdl
  have hStab : Stab A s⁻¹ := fun y => by
    have := hSt (s⁻¹ y)
    rw [show s (s⁻¹ y) = y from s.apply_symm_apply y] at this
    exact this.symm
  have hzL : s⁻¹ (zt ε l (m + n)) = zt ε l (m + n) :=
    (mem_fixMu_iff _).1 hsi _ ((zt_pow ε hl0 _).pow_eq_one_iff_dvd _ |>.2 (Dvd.intro _ rfl))
  have hzn : s⁻¹ (zt ε l n) = zt ε l n :=
    (mem_fixMu_iff _).1 hsi _ ((zt_pow ε hl0 _).pow_eq_one_iff_dvd _ |>.2 hlM)
  have hgalF : ∀ f : topF X (topMu l n m N), X.gal s⁻¹ (e (algebraMap (topF X (topMu l n m N)) (topL X (topMu l n m N)) f)) =
      e (algebraMap (topF X (topMu l n m N)) (topL X (topMu l n m N)) f) := fun f => by
    have hf := (mem_mdl_iff X _ _ _).1 f.2
    rw [he]
    show X.gal s⁻¹ (X.sl _ (X.sl _ (f : X.K))) = X.sl _ (X.sl _ (f : X.K))
    rw [gal_sl_diag X hNN, gal_sl_g X hMM hsi g hf.1, hf.2 _ hsi]
  have hlift := isTopLift_topLift X hMM hs
  have hσ : ∀ k k' : topL X (topMu l n m N), e k' = X.gal s⁻¹ (e k) →
      ((topLift X (topMu l n m N) s)⁻¹) (algebraMap (topL X (topMu l n m N)) (topBar X (topMu l n m N)) k) =
        algebraMap (topL X (topMu l n m N)) (topBar X (topMu l n m N)) k' := fun k k' hk => by
    rw [he, he, gal_sl_diag X hNN, gal_sl_g X hMM hsi g k.2] at hk
    have hk' : (k' : X.K) = X.gal s⁻¹ k := (X.sl (ofSL g)).injective ((X.sl _).injective hk)
    obtain ⟨f', ef, hf'⟩ := hlift k'
    have : f' = k := Subtype.ext (by rw [ef, hk', ← gal_mul_apply, mul_inv_cancel, gal_one_apply])
    rw [← this, ← hf', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have htv : ∃ v : ℕ, t.val + (-t).val = l ^ n * v := by
    have h0 : ((t.val + (-t).val : ℕ) : ZMod (l ^ n)) = 0 := by
      haveI : NeZero (l ^ n) := ⟨pow_ne_zero n hl0⟩
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, add_neg_cancel]
    exact (ZMod.natCast_eq_zero_iff _ _).1 h0
  obtain ⟨v, hv⟩ := htv
  have hzt1 : zt ε l n ^ t.val * zt ε l n ^ (-t).val = 1 := by
    rw [← pow_add, hv, pow_mul, (zt_pow ε hl0 n).pow_eq_one, one_pow]
  have hzz : s⁻¹ (zt ε l (m + n + n)) = zt ε l n ^ (-t).val * zt ε l (m + n + n) := by
    have h1 := congrArg (s⁻¹ : Ω ≃ₐ[ℚ] Ω) ht
    rw [show s⁻¹ (s (zt ε l (m + n + n))) = zt ε l (m + n + n) from s.symm_apply_apply _, map_mul, map_pow, hzn] at h1
    calc s⁻¹ (zt ε l (m + n + n)) = (zt ε l n ^ t.val * zt ε l n ^ (-t).val) * s⁻¹ (zt ε l (m + n + n)) := by
          rw [hzt1, one_mul]
      _ = zt ε l n ^ (-t).val * (zt ε l n ^ t.val * s⁻¹ (zt ε l (m + n + n))) := by ring
      _ = zt ε l n ^ (-t).val * zt ε l (m + n + n) := by rw [← h1]
  have hfin := hmain s⁻¹ hStab hzL hgalF _ hσ _ φ' (-t) (TopW.isTopW_topW_of_exists (hW _)) hdl hzz (r * ((N * N : ℕ) : ℚ))
  have hcnd : ∀ e : ℕ, Nat.Coprime e (6 * l * N) → ∀ a : ℤ, ¬ (l : ℤ) ∣ a → ¬ (l : ℤ) ∣ (e : ℤ) * a := fun e he a ha h => by
    rcases hlZ.dvd_or_dvd h with h | h
    · exact hnd e he h
    · exact ha h
  have hres := resc ε (N ^ 2) (N * l ^ (m + n)) c d (l ^ (m + n)) (en g 0 0 * w1) ((N : ℤ) ^ 2 * en g 0 1) w2 ((N : ℤ) * en g 1 1)
    (pow_pos hN0 2) hM0 (pow_pos hlp.pos _) (not_dvd_of hMl hA1) (not_dvd_of hMl (hcnd c hP.cc _ hA1))
    (not_dvd_of hMl hB1) (not_dvd_of hMl (hcnd d hP.dc _ hB1)) (r * ((N * N : ℕ) : ℚ))
  have hNeq : N ^ 2 * (N * l ^ (m + n)) = N ^ 3 * l ^ (m + n) := by ring
  have hcz : ((N ^ 2 : ℕ) : ℤ) = (N : ℤ) ^ 2 := by push_cast; rfl
  have hrq : r * ((N * N : ℕ) : ℚ) / ((N ^ 2 : ℕ) : ℚ) = r := by
    rw [show N ^ 2 = N * N by ring]
    exact mul_div_cancel_right₀ _ hD0.ne'
  rw [hNeq, hcz, hrq] at hres
  have hEr : EE ε l (m + n) N x c d g r = coefQ (l ^ (m + n)) (cmul (smF c 1 (N * l ^ (m + n)) (eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ))) (en g 0 0 * w1) ((N : ℤ) ^ 2 * en g 0 1))
      (smF d 1 (N * l ^ (m + n)) (eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ))) w2 ((N : ℤ) * en g 1 1))) r := rfl
  rw [← hEr] at hres
  obtain ⟨z0, hz0, e0⟩ := hfin
  rw [hres, hφ', mul_div_cancel_right₀ _ hD0.ne'] at e0
  have e1 : (s⁻¹ : Ω ≃ₐ[ℚ] Ω).symm (ξ (r * ((N * N : ℕ) : ℚ))) = s (ξ (r * ((N * N : ℕ) : ℚ))) := rfl
  rw [e1] at e0
  have hdet : en g 0 0 * en g 1 1 - en g 0 1 * en g 1 0 = 1 := by
    have := g.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  have hZ : (N : ℤ) ^ 2 * (en g 0 0 * w1) * en g 1 1 - (N : ℤ) * en g 0 1 * ((N : ℤ) ^ 2 * w2) =
      (N : ℤ) ^ 3 + (l : ℤ) ^ (m + n) * ((N : ℤ) ^ 2 * en g 0 0 * (x.val : ℤ) * (topT l (m + n) N : ℤ) * en g 1 1 -
        (N : ℤ) ^ 3 * en g 0 1 * en g 0 0 * (topT l (m + n) N : ℤ)) := by
    rw [hw1, hw2]
    linear_combination (N : ℤ) ^ 3 * hdet
  set Q : ℤ := (N : ℤ) ^ 2 * en g 0 0 * (x.val : ℤ) * (topT l (m + n) N : ℤ) * en g 1 1 -
        (N : ℤ) ^ 3 * en g 0 1 * en g 0 0 * (topT l (m + n) N : ℤ) with hQ
  have hZΩ : (((N : ℤ) ^ 2 * (en g 0 0 * w1) * en g 1 1 - (N : ℤ) * en g 0 1 * ((N : ℤ) ^ 2 * w2) : ℤ) : Ω) =
      (N : Ω) ^ 3 + (l : Ω) ^ (m + n) * (Q : Ω) := by
    rw [hZ]; push_cast; rfl
  have hvΩ : (t.val : Ω) + ((-t).val : Ω) = (l : Ω) ^ n * (v : Ω) := by exact_mod_cast congrArg (Nat.cast (R := Ω)) hv
  refine ⟨z0 - (l : Ω) ^ cc * EE ε l (m + n) N x c d g r * ((N : Ω) ^ 3 * (v : Ω) + (l : Ω) ^ m * (Q : Ω) * ((-t).val : Ω)),
    sub_mem hz0 (mul_mem (mul_mem (pow_mem (natCast_mem A l) _) (hEE r))
      (add_mem (mul_mem (pow_mem (natCast_mem A N) _) (natCast_mem A v))
        (mul_mem (mul_mem (pow_mem (natCast_mem A l) _) (intCast_mem A Q)) (natCast_mem A _)))), ?_⟩
  beta_reduce
  linear_combination e0 - (l : Ω) ^ cc * ((-t).val : Ω) * EE ε l (m + n) N x c d g r * hZΩ -
    (l : Ω) ^ cc * (N : Ω) ^ 3 * EE ε l (m + n) N x c d g r * hvΩ
