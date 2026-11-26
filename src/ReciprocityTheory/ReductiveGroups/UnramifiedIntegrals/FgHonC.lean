module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgBasic

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonB
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Ev

variable {R : Type} [CommRing R]

def ev0 (F : MvPowerSeries (Fin 2) R) : PowerSeries R :=
  MvPowerSeries.subst ![(X : PowerSeries R), 0] F

theorem coeff_evalYZero (F : MvPowerSeries (Fin 2) R) (n : ℕ) :
    coeff n (ev0 F) = MvPowerSeries.coeff (Finsupp.single 0 n) F := by
  have ha : MvPowerSeries.HasSubst ![(X : PowerSeries R), 0] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun i => by fin_cases i <;> first | exact PowerSeries.constantCoeff_X | simp)
  have hc : ∀ f : PowerSeries R, MvPowerSeries.coeff (Finsupp.single () n) f = coeff n f := fun f => rfl
  have h := MvPowerSeries.coeff_subst ha F (Finsupp.single () n)
  unfold ev0
  rw [← hc, h, finsum_eq_single _ (Finsupp.single 0 n)]
  · rw [Finsupp.prod_single_index (by simp), hc]
    simp
  · intro d hd
    rw [hc, Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    by_cases h1 : d 1 = 0
    · rw [h1, pow_zero, mul_one, coeff_X_pow, if_neg, smul_zero]
      intro h0
      apply hd
      ext i
      fin_cases i
      · simp [h0]
      · simp [h1]
    · rw [zero_pow h1, mul_zero, map_zero, smul_zero]

theorem evalYZero_add (F G : MvPowerSeries (Fin 2) R) : ev0 (F + G) = ev0 F + ev0 G := by
  have ha : MvPowerSeries.HasSubst ![(X : PowerSeries R), 0] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> first | exact PowerSeries.constantCoeff_X | simp)
  unfold ev0
  rw [MvPowerSeries.subst_add ha]

theorem evalYZero_mul (F G : MvPowerSeries (Fin 2) R) : ev0 (F * G) = ev0 F * ev0 G := by
  have ha : MvPowerSeries.HasSubst ![(X : PowerSeries R), 0] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> first | exact PowerSeries.constantCoeff_X | simp)
  unfold ev0
  rw [MvPowerSeries.subst_mul ha]

theorem evalYZero_subst (φ : PowerSeries R) {P : MvPowerSeries (Fin 2) R}
    (hP : MvPowerSeries.constantCoeff P = 0) : ev0 (φ.subst P) = φ.subst (ev0 P) := by
  have ha : MvPowerSeries.HasSubst ![(X : PowerSeries R), 0] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun i => by fin_cases i <;> first | exact PowerSeries.constantCoeff_X | simp)
  have hP' : MvPowerSeries.HasSubst (fun _ : Unit => P) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hP)
  unfold ev0
  unfold PowerSeries.subst
  exact MvPowerSeries.subst_comp_subst_apply hP' ha φ

private theorem mvPowerSeries_coeff_subst_X_eq_ite_single {S : Type} [CommRing S] {ι : Type} [DecidableEq ι] (i : ι) (f : PowerSeries S)
    (e : ι →₀ ℕ) :
    MvPowerSeries.coeff e (f.subst (MvPowerSeries.X i : MvPowerSeries ι S)) =
      if e = Finsupp.single i (e i) then coeff (e i) f else 0 := by
  have ha : HasSubst (MvPowerSeries.X i : MvPowerSeries ι S) :=
    HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  rw [PowerSeries.coeff_subst ha]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  split_ifs with h
  · rw [finsum_eq_single _ (e i)]
    · rw [if_pos h]
    · intro d hd
      rw [if_neg]
      intro he
      exact hd (by rw [he, Finsupp.single_eq_same])
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    rw [if_neg]
    intro he
    exact h (by rw [he, Finsupp.single_eq_same])

theorem evalYZero_atX (φ : PowerSeries R) : ev0 (atX φ) = φ := by
  ext n
  rw [coeff_evalYZero]
  unfold atX
  rw [mvPowerSeries_coeff_subst_X_eq_ite_single]
  simp

theorem evalYZero_atY (φ : PowerSeries R) : ev0 (atY φ) = C (constantCoeff φ) := by
  ext n
  rw [coeff_evalYZero, coeff_C]
  unfold atY
  rw [mvPowerSeries_coeff_subst_X_eq_ite_single]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg (show ¬ n = 0 by omega), if_neg]
    intro h
    have h1 := congrArg (fun e => e 0) h
    simp at h1
    omega

end Ev

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K}

theorem partialYAtZero_eq (F : MvPowerSeries (Fin 2) K) : d2 F = ev0 (MvPowerSeries.pderiv (R := K) 1 F) := by
  ext n
  rw [coeff_evalYZero, MvPowerSeries.coeff_pderiv]
  simp [d2]

theorem integralPS_partialYAtZero (hΦ : IntegralMv Φ) : IntegralPS (d2 Φ) := by
  unfold IntegralMv at hΦ
  unfold IntegralPS d2
  intro n
  rw [coeff_mk]
  exact hΦ _

theorem divBy_partialYAtZero {x : K} {F : MvPowerSeries (Fin 2) K} (hF : DivByMv x F) : DivBy x (d2 F) := by
  unfold DivByMv at hF
  unfold DivBy d2
  intro n
  rw [coeff_mk]
  exact hF _

theorem partialYAtZero_subst (D : PowerSeries K) {P : MvPowerSeries (Fin 2) K}
    (hP : MvPowerSeries.constantCoeff P = 0) :
    d2 (D.subst P) = (derivative D).subst (ev0 P) * d2 P := by
  rw [partialYAtZero_eq, Formalism.G.LogCR.pderiv_psubst hP, evalYZero_mul, evalYZero_subst _ hP, partialYAtZero_eq]

theorem partialYAtZero_atX (D : PowerSeries K) : d2 (atX D) = 0 := by
  ext n
  unfold d2 atX
  rw [coeff_mk, mvPowerSeries_coeff_subst_X_eq_ite_single, if_neg, map_zero]
  intro h
  have h1 := congrArg (fun e => e 1) h
  simp at h1

theorem partialYAtZero_atY (D : PowerSeries K) : d2 (atY D) = C (coeff 1 D) := by
  ext n
  unfold d2 atY
  rw [coeff_mk, mvPowerSeries_coeff_subst_X_eq_ite_single, coeff_C]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg (show ¬ n = 0 by omega), if_neg]
    intro h
    have h1 := congrArg (fun e => e 0) h
    simp at h1
    omega

theorem partialYAtZero_sub (F G : MvPowerSeries (Fin 2) K) : d2 (F - G) = d2 F - d2 G := by
  ext n
  simp only [d2, PowerSeries.coeff_mk, map_sub]

theorem partialYAtZero_add (F G : MvPowerSeries (Fin 2) K) : d2 (F + G) = d2 F + d2 G := by
  ext n
  simp only [d2, PowerSeries.coeff_mk, map_add (f := _)]

theorem LawD.evalYZero_eq (h : LawD lam Φ) : ev0 Φ = X := by
  have hc : constantCoeff (ev0 Φ) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_evalYZero, Finsupp.single_zero,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h.Φ0
  have h1 := congrArg ev0 h.log
  rw [evalYZero_subst lam h.Φ0, evalYZero_add, evalYZero_atX, evalYZero_atY, h.lam0, map_zero, add_zero] at h1
  have hu : IsUnit (coeff 1 lam) := by rw [h.lam1]; exact isUnit_one
  have hl : HasSubst lam := HasSubst.of_constantCoeff_zero h.lam0
  have he : HasSubst (ev0 Φ) := HasSubst.of_constantCoeff_zero hc
  have h2 := PowerSeries.subst_comp_subst_apply hl he (lam.substInvOfIsUnit hu)
  rw [PowerSeries.subst_substInvOfIsUnit_left lam h.lam0 hu, PowerSeries.subst_X he, h1,
    PowerSeries.subst_substInvOfIsUnit_left lam h.lam0 hu] at h2
  exact h2

private theorem powerSeries_subst_X_self_commRing {S : Type} [CommRing S] (t : PowerSeries S) :
    t.subst (X : PowerSeries S) = t := by
  ext n
  rw [PowerSeries.coeff_subst' (HasSubst.of_constantCoeff_zero constantCoeff_X), finsum_eq_single _ n]
  · simp
  · intro d hd
    simp [coeff_X_pow, Ne.symm hd]

theorem LawD.coeffY_subst (h : LawD lam Φ) (D : PowerSeries K) :
    d2 (D.subst Φ) = derivative D * d2 Φ := by
  rw [partialYAtZero_subst D h.Φ0, h.evalYZero_eq, powerSeries_subst_X_self_commRing]

theorem LawD.deriv_mul (h : LawD lam Φ) : derivative lam * d2 Φ = 1 := by
  have h1 := congrArg d2 h.log
  rw [h.coeffY_subst, partialYAtZero_add, partialYAtZero_atX, partialYAtZero_atY, h.lam1, zero_add, map_one] at h1
  exact h1

theorem LawD.deriv_const (h : LawD lam Φ) : constantCoeff (derivative lam) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
  simp [h.lam1]

theorem LawD.constantCoeff_partialYAtZero (h : LawD lam Φ) : constantCoeff (d2 Φ) = 1 := by
  have h1 := congrArg constantCoeff h.deriv_mul
  rw [map_mul, h.deriv_const, one_mul, map_one] at h1
  exact h1

theorem LawD.deriv_integral (h : LawD lam Φ) : IntegralPS (derivative lam) := by
  have hm := h.deriv_mul
  have ha := integralPS_partialYAtZero h.Φint
  have h0 := h.constantCoeff_partialYAtZero
  unfold IntegralPS at ha ⊢
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [h.deriv_const]
    · have hc := congrArg (coeff n) hm
      simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
        Nat.sub_self, coeff_zero_eq_constantCoeff_apply, h0, mul_one, coeff_one,
        if_neg (show n ≠ 0 by omega)] at hc
      have e : coeff n (derivative lam) =
          -∑ k ∈ Finset.range n, coeff k (derivative lam) * coeff (n - k) (d2 Φ) := by
        linear_combination hc
      rw [e, norm_neg]
      refine Finset.sum_induction _ (fun x => ‖x‖ ≤ 1)
        (fun x y hx hy => (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy))
        (by simp) fun k hk => ?_
      rw [norm_mul]
      have hk' := Finset.mem_range.mp hk
      calc ‖coeff k (derivative lam)‖ * ‖coeff (n - k) (d2 Φ)‖ ≤ 1 * 1 :=
            mul_le_mul (ih k hk') (ha _) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

theorem hon_deriv (h : LawD lam Φ) (x : K) (D : PowerSeries K)
    (hadd : DivByMv x (D.subst Φ - atX D - atY D)) :
    DivBy x (derivative D - C (coeff 1 D) * derivative lam) := by
  have h1 := divBy_partialYAtZero hadd
  rw [partialYAtZero_sub, partialYAtZero_sub, h.coeffY_subst, partialYAtZero_atX, partialYAtZero_atY, sub_zero] at h1
  have e : derivative D - C (coeff 1 D) * derivative lam =
      derivative lam * (derivative D * d2 Φ - C (coeff 1 D)) := by
    linear_combination (-derivative D) * h.deriv_mul
  rw [e]
  have hl := h.deriv_integral
  unfold DivBy at h1 ⊢
  unfold IntegralPS at hl
  intro n
  rw [coeff_mul]
  refine Finset.sum_induction _ (fun y => ‖y‖ ≤ ‖x‖)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
    (by simp) fun p _ => ?_
  rw [norm_mul]
  calc ‖coeff p.1 (derivative lam)‖ * ‖coeff p.2 (derivative D * d2 Φ - C (coeff 1 D))‖
        ≤ 1 * ‖x‖ := mul_le_mul (hl _) (h1 _) (norm_nonneg _) zero_le_one
    _ = ‖x‖ := one_mul _

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonA
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

private theorem norm_finsum_le_of_forall_norm_le_univ_sort {α : Type*} (f : α → K) {C : ℝ} (hC : 0 ≤ C) (h : ∀ a, ‖f a‖ ≤ C) :
    ‖∑ᶠ a, f a‖ ≤ C := by
  classical
  rw [finsum_def]
  split_ifs with hs
  · exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun i _ => h i
  · simpa using hC

private theorem mvPowerSeries_norm_coeff_mul_le_mul {ι : Type} {F G : MvPowerSeries ι K} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : ∀ e, ‖MvPowerSeries.coeff e F‖ ≤ a) (hG : ∀ e, ‖MvPowerSeries.coeff e G‖ ≤ b) :
    ∀ e, ‖MvPowerSeries.coeff e (F * G)‖ ≤ a * b := by
  classical
  intro e
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun p _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hF _) (hG _) (norm_nonneg _) ha

private theorem mvPowerSeries_norm_coeff_pow_le_pow {ι : Type} {F : MvPowerSeries ι K} {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ e, ‖MvPowerSeries.coeff e F‖ ≤ c) :
    ∀ (m : ℕ) (e : ι →₀ ℕ), ‖MvPowerSeries.coeff e (F ^ m)‖ ≤ c ^ m := by
  classical
  intro m
  induction m with
  | zero =>
    intro e
    rw [pow_zero, pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact mvPowerSeries_norm_coeff_mul_le_mul (pow_nonneg hc m) hc ih hF

private theorem mvPowerSeries_norm_coeff_pow_le_one {ι : Type} {F : MvPowerSeries ι K}
    (hF : ∀ e, ‖MvPowerSeries.coeff e F‖ ≤ 1) (m : ℕ) (e : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff e (F ^ m)‖ ≤ 1 := by
  simpa using mvPowerSeries_norm_coeff_pow_le_pow zero_le_one hF m e

private theorem mvPowerSeries_norm_coeff_pow_sub_pow_le {ι : Type} {A B : MvPowerSeries ι K} {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ e, ‖MvPowerSeries.coeff e A‖ ≤ 1) (hB : ∀ e, ‖MvPowerSeries.coeff e B‖ ≤ 1)
    (hAB : ∀ e, ‖MvPowerSeries.coeff e (A - B)‖ ≤ c) (m : ℕ) (e : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff e (A ^ m - B ^ m)‖ ≤ c := by
  classical
  have hs : ∀ e, ‖MvPowerSeries.coeff e (∑ i ∈ Finset.range m, A ^ i * B ^ (m - 1 - i))‖ ≤ 1 := by
    intro e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    simpa using mvPowerSeries_norm_coeff_mul_le_mul zero_le_one zero_le_one (mvPowerSeries_norm_coeff_pow_le_one hA i) (mvPowerSeries_norm_coeff_pow_le_one hB (m - 1 - i)) e
  rw [← geom_sum₂_mul]
  simpa using mvPowerSeries_norm_coeff_mul_le_mul zero_le_one hc hs hAB e

private theorem mvPowerSeries_norm_coeff_pow_prime_sub_le_mul_norm {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {A B : MvPowerSeries ι K}
    {c : ℝ} (hc : 0 ≤ c) (hcl : c ≤ ‖(l : K)‖) (hB : ∀ e, ‖MvPowerSeries.coeff e B‖ ≤ 1)
    (hAB : ∀ e, ‖MvPowerSeries.coeff e (A - B)‖ ≤ c) (e : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff e (A ^ l - B ^ l)‖ ≤ c * ‖(l : K)‖ := by
  classical
  obtain ⟨D, rfl⟩ : ∃ D, A = D + B := ⟨A - B, by ring⟩
  simp only [add_sub_cancel_right] at hAB
  have hc1 : c ≤ 1 := hcl.trans hl1.le
  have hl2 : 2 ≤ l := hl.two_le
  rw [add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
    add_sub_cancel_right]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc (norm_nonneg _))
    fun i hi => ?_
  have hi' : i < l := Finset.mem_range.mp hi
  rw [← Nat.cast_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, norm_mul]
  have hterm : ‖MvPowerSeries.coeff e (D ^ (i + 1) * B ^ (l - (i + 1)))‖ ≤ c ^ (i + 1) := by
    simpa using mvPowerSeries_norm_coeff_mul_le_mul (pow_nonneg hc _) zero_le_one (mvPowerSeries_norm_coeff_pow_le_pow hc hAB (i + 1)) (mvPowerSeries_norm_coeff_pow_le_one hB _) e
  have hch : ‖((l.choose (i + 1) : ℕ) : K)‖ * c ^ (i + 1) ≤ c * ‖(l : K)‖ := by
    obtain h | h : i + 1 < l ∨ i + 1 = l := by omega
    · obtain ⟨q, hq⟩ := hl.dvd_choose_self (Nat.succ_ne_zero i) h
      rw [hq, Nat.cast_mul, norm_mul]
      have hq1 : ‖(q : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K q
      have hpc : c ^ (i + 1) ≤ c := pow_le_of_le_one hc hc1 (Nat.succ_ne_zero i)
      calc ‖(l : K)‖ * ‖(q : K)‖ * c ^ (i + 1) ≤ ‖(l : K)‖ * 1 * c := by
            gcongr
        _ = c * ‖(l : K)‖ := by ring
    · rw [h, Nat.choose_self, Nat.cast_one, norm_one, one_mul]
      obtain ⟨j, rfl⟩ : ∃ j, l = j + 2 := ⟨l - 2, by omega⟩
      have hpc : c ^ (j + 1) ≤ c := pow_le_of_le_one hc hc1 (Nat.succ_ne_zero j)
      calc c ^ (j + 2) = c * c ^ (j + 1) := by ring
        _ ≤ c * ‖((j + 2 : ℕ) : K)‖ := by gcongr; exact hpc.trans hcl
  calc ‖((l.choose (i + 1) : ℕ) : K)‖ * ‖MvPowerSeries.coeff e (D ^ (i + 1) * B ^ (l - (i + 1)))‖
      ≤ ‖((l.choose (i + 1) : ℕ) : K)‖ * c ^ (i + 1) := by gcongr
    _ ≤ c * ‖(l : K)‖ := hch

private theorem mvPowerSeries_norm_coeff_pow_prime_pow_sub_le {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {P Q : MvPowerSeries ι K}
    (hQ : ∀ e, ‖MvPowerSeries.coeff e Q‖ ≤ 1)
    (hPQ : ∀ e, ‖MvPowerSeries.coeff e (P - Q)‖ ≤ ‖(l : K)‖) :
    ∀ (v : ℕ) (e : ι →₀ ℕ), ‖MvPowerSeries.coeff e (P ^ (l ^ v) - Q ^ (l ^ v))‖ ≤ ‖(l : K)‖ ^ (v + 1) := by
  intro v
  induction v with
  | zero => simpa using hPQ
  | succ v ih =>
    intro e
    rw [pow_succ, pow_mul, pow_mul, pow_succ _ (v + 1)]
    exact mvPowerSeries_norm_coeff_pow_prime_sub_le_mul_norm hl hl1 (pow_nonneg (norm_nonneg _) _)
      (pow_le_of_le_one (norm_nonneg _) hl1.le (Nat.succ_ne_zero v)) (mvPowerSeries_norm_coeff_pow_le_one hQ _) ih e

private theorem norm_natCast_eq_one_of_not_prime_dvd (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {m : ℕ} (hm : ¬ l ∣ m) :
    ‖(m : K)‖ = 1 := by
  have hcop : Nat.Coprime l m := (Nat.coprime_or_dvd_of_prime hl m).resolve_right hm
  have h1 := Nat.gcd_eq_gcd_ab l m
  rw [hcop.gcd_eq_one] at h1
  have h2 : (1 : K) = (l : K) * (Nat.gcdA l m : K) + (m : K) * (Nat.gcdB l m : K) := by
    have h3 := congrArg (fun x : ℤ => (x : K)) h1
    push_cast at h3
    exact h3
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K m) (not_lt.mp fun hlt => ?_)
  have h4 : ‖(1 : K)‖ < 1 := by
    rw [h2]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      calc ‖(l : K)‖ * ‖((Nat.gcdA l m : ℤ) : K)‖ ≤ ‖(l : K)‖ * 1 := by
            gcongr
            exact IsUltrametricDist.norm_intCast_le_one K _
        _ < 1 := by simpa using hl1
    · rw [norm_mul]
      calc ‖(m : K)‖ * ‖((Nat.gcdB l m : ℤ) : K)‖ ≤ ‖(m : K)‖ * 1 := by
            gcongr
            exact IsUltrametricDist.norm_intCast_le_one K _
        _ < 1 := by simpa using hlt
  simp at h4

theorem qls {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (z : PowerSeries K)
    (hz0 : constantCoeff z = 0) (hz : IntegralPS (derivative z)) (P Q : MvPowerSeries ι K)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hQ0 : MvPowerSeries.constantCoeff Q = 0)
    (hP : IntegralMv P) (hQ : IntegralMv Q) (hPQ : DivByMv (l : K) (P - Q)) :
    DivByMv (l : K) (z.subst P - z.subst Q) := by
  classical
  have hPs : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  have hQs : PowerSeries.HasSubst Q := PowerSeries.HasSubst.of_constantCoeff_zero hQ0
  have hPi : ∀ e, ‖MvPowerSeries.coeff e P‖ ≤ 1 := by
    unfold IntegralMv at hP
    exact hP
  have hQi : ∀ e, ‖MvPowerSeries.coeff e Q‖ ≤ 1 := by
    unfold IntegralMv at hQ
    exact hQ
  have hPQi : ∀ e, ‖MvPowerSeries.coeff e (P - Q)‖ ≤ ‖(l : K)‖ := by
    unfold DivByMv at hPQ
    exact hPQ
  have hzi : ∀ n, ‖PowerSeries.coeff n (derivative z)‖ ≤ 1 := by
    unfold IntegralPS at hz
    exact hz
  have hpow := mvPowerSeries_norm_coeff_pow_prime_pow_sub_le hl hl1 hQi hPQi
  have hterm : ∀ (d : ℕ) (e : ι →₀ ℕ),
      ‖PowerSeries.coeff d z • MvPowerSeries.coeff e (P ^ d) -
        PowerSeries.coeff d z • MvPowerSeries.coeff e (Q ^ d)‖ ≤ ‖(l : K)‖ := by
    intro d e
    rw [← smul_sub, ← map_sub, norm_smul]
    rcases d with _ | k
    · have h0 : PowerSeries.coeff 0 z = 0 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact hz0
      rw [h0, norm_zero, zero_mul]
      exact norm_nonneg _
    · obtain ⟨v, m, hm, hkm0⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.succ_ne_zero k) l hl.ne_one
      have hkm : k + 1 = l ^ v * m := hkm0
      have hz' : ‖PowerSeries.coeff (k + 1) z‖ * ‖((k + 1 : ℕ) : K)‖ ≤ 1 := by
        have h1 := hzi k
        rw [PowerSeries.coeff_derivative] at h1
        simpa [norm_mul] using h1
      have hn : ‖((k + 1 : ℕ) : K)‖ = ‖(l : K)‖ ^ v := by
        rw [hkm, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, norm_natCast_eq_one_of_not_prime_dvd hl hl1 hm, mul_one]
      have hPQn : ‖MvPowerSeries.coeff e (P ^ (k + 1) - Q ^ (k + 1))‖ ≤ ‖(l : K)‖ ^ (v + 1) := by
        rw [hkm, pow_mul, pow_mul]
        exact mvPowerSeries_norm_coeff_pow_sub_pow_le (pow_nonneg (norm_nonneg _) _) (mvPowerSeries_norm_coeff_pow_le_one hPi _) (mvPowerSeries_norm_coeff_pow_le_one hQi _) (hpow v) m e
      calc ‖PowerSeries.coeff (k + 1) z‖ * ‖MvPowerSeries.coeff e (P ^ (k + 1) - Q ^ (k + 1))‖
          ≤ ‖PowerSeries.coeff (k + 1) z‖ * ‖(l : K)‖ ^ (v + 1) := by gcongr
        _ = (‖PowerSeries.coeff (k + 1) z‖ * ‖((k + 1 : ℕ) : K)‖) * ‖(l : K)‖ := by
          rw [hn, pow_succ, mul_assoc]
        _ ≤ 1 * ‖(l : K)‖ := by gcongr
        _ = ‖(l : K)‖ := one_mul _
  unfold DivByMv
  intro e
  rw [map_sub, PowerSeries.coeff_subst hPs, PowerSeries.coeff_subst hQs,
    ← finsum_sub_distrib (PowerSeries.coeff_subst_finite hPs z e)
      (PowerSeries.coeff_subst_finite hQs z e)]
  exact norm_finsum_le_of_forall_norm_le_univ_sort _ (norm_nonneg _) fun d => hterm d e

theorem qls1 (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (z : PowerSeries K)
    (hz0 : constantCoeff z = 0) (hz : IntegralPS (derivative z)) (P Q : PowerSeries K)
    (hP0 : constantCoeff P = 0) (hQ0 : constantCoeff Q = 0)
    (hP : IntegralPS P) (hQ : IntegralPS Q) (hPQ : DivBy (l : K) (P - Q)) :
    DivBy (l : K) (z.subst P - z.subst Q) := by
  have key : ∀ (F : PowerSeries K) (d : Unit →₀ ℕ),
      MvPowerSeries.coeff d F = PowerSeries.coeff (d ()) F := by
    intro F d
    conv_lhs => rw [Finsupp.unique_single d]
    rfl
  have hP' : IntegralMv P := by
    unfold IntegralMv
    intro d
    rw [key]
    exact hP _
  have hQ' : IntegralMv Q := by
    unfold IntegralMv
    intro d
    rw [key]
    exact hQ _
  have hPQ' : DivByMv (l : K) (P - Q) := by
    unfold DivByMv
    intro d
    rw [key]
    exact hPQ _
  have h := qls hl hl1 z hz0 hz P Q hP0 hQ0 hP' hQ' hPQ'
  unfold DivBy
  intro k
  have hk := h (Finsupp.single () k)
  rwa [key, Finsupp.single_eq_same] at hk

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

theorem desc_const (D : PowerSeries K) : constantCoeff (desc l D) = constantCoeff D := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    desc, PowerSeries.coeff_mk, mul_zero]

theorem desc_integral {D : PowerSeries K} (hD : IntegralPS D) : IntegralPS (desc l D) := by
  unfold IntegralPS at hD ⊢
  intro n
  rw [desc, PowerSeries.coeff_mk]
  exact hD _

theorem coeff_one_desc (D : PowerSeries K) : coeff 1 (desc l D) = coeff l D := by
  rw [desc, PowerSeries.coeff_mk, mul_one]

private theorem coeff_subst_X_pow_lemma (f : PowerSeries K) {k : ℕ} (hk : k ≠ 0) (m : ℕ) :
    coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
  have ha : PowerSeries.HasSubst ((X : PowerSeries K) ^ k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hk])
  rw [PowerSeries.coeff_subst' ha]
  simp only [← pow_mul, PowerSeries.coeff_X_pow]
  split_ifs with hd
  · obtain ⟨q, rfl⟩ := hd
    rw [finsum_eq_single _ q]
    · simp [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hk)]
    · intro d hd
      have : k * q ≠ k * d := fun h => hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h).symm
      simp [this]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    have : m ≠ k * d := fun h => hd ⟨d, h⟩
    simp [this]

theorem desc_congr (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (D : PowerSeries K)
    (hD : DivBy (l : K) (PowerSeries.derivative D)) :
    DivBy (l : K) (D - (desc l D).subst ((X : PowerSeries K) ^ l)) ∧
      IntegralPS (PowerSeries.derivative (desc l D)) := by
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hlpos : 0 < ‖(l : K)‖ := norm_pos_iff.mpr hl0
  have hD' : ∀ n, ‖coeff n (PowerSeries.derivative D)‖ ≤ ‖(l : K)‖ := hD
  have hD2 : ∀ m, ‖coeff (m + 1) D‖ * ‖((m : K) + 1)‖ ≤ ‖(l : K)‖ := by
    intro m
    have h := hD' m
    rwa [PowerSeries.coeff_derivative, norm_mul] at h
  refine ⟨?_, ?_⟩
  · intro m
    rw [map_sub, coeff_subst_X_pow_lemma _ hl.ne_zero]
    split_ifs with hd
    · obtain ⟨q, rfl⟩ := hd
      rw [desc, PowerSeries.coeff_mk, Nat.mul_div_cancel_left q hl.pos, sub_self, norm_zero]
      exact norm_nonneg _
    · rw [sub_zero]
      have hm0 : m ≠ 0 := fun h => hd (h ▸ dvd_zero l)
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have h1 := hD2 m'
      have hu : ‖((m' : K) + 1)‖ = 1 := by
        have h2 := norm_natCast_of_coprime hl hl1 (m' + 1) hd
        push_cast at h2
        exact h2
      rwa [hu, mul_one] at h1
  · intro m
    rw [PowerSeries.coeff_derivative, desc, PowerSeries.coeff_mk, norm_mul]
    have e : l * (m + 1) - 1 + 1 = l * (m + 1) :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hl.ne_zero (Nat.succ_ne_zero m)))
    have e2 : ((l * (m + 1) - 1 : ℕ) : K) + 1 = (l : K) * ((m : K) + 1) := by
      rw [← Nat.cast_add_one, e]
      push_cast
      ring
    have h1 := hD2 (l * (m + 1) - 1)
    rw [e2, e, norm_mul] at h1
    have h2 : ‖(l : K)‖ * (‖coeff (l * (m + 1)) D‖ * ‖((m : K) + 1)‖) ≤ ‖(l : K)‖ * 1 := by
      linarith [h1]
    exact le_of_mul_le_mul_left h2 hlpos

theorem desc_key {ι : Type} (hF : FrobField K l σ) {D : PowerSeries K}
    (hD0 : constantCoeff D = 0) (hD' : DivBy (l : K) (PowerSeries.derivative D)) (P : MvPowerSeries ι K)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv (l : K) (MvPowerSeries.expand l hF.prime.ne_zero
      ((desc l D).subst (MvPowerSeries.map σ P)) - D.subst P) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  obtain ⟨h1, h2⟩ := desc_congr hF.prime hF.norm_l D hD'
  have hσP0 : MvPowerSeries.constantCoeff (MvPowerSeries.map σ P) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hP0, map_zero]
  have hPs : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  rw [PowerSeries.expand_subst l hl0 (PowerSeries.HasSubst.of_constantCoeff_zero hσP0)]
  have hfc := FrobCongr_valid K l l hl0 σ hF.funEqSetting ι P hP
  have hE0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.expand l hl0 (MvPowerSeries.map σ P)) = 0 := by
    rw [MvPowerSeries.constantCoeff_expand, hσP0]
  have hEi : IntegralMv (MvPowerSeries.expand l hl0 (MvPowerSeries.map σ P)) := by
    rw [integralMv_iff_divBy_one, divByMv_expand_iff, ← integralMv_iff_divBy_one]
    exact hF.integralMv_map hP
  have hPl0 : MvPowerSeries.constantCoeff (P ^ l) = 0 := by
    rw [map_pow, hP0, zero_pow hl0]
  have h3 := qls hF.prime hF.norm_l (desc l D) (by rw [desc_const, hD0]) h2
    (MvPowerSeries.expand l hl0 (MvPowerSeries.map σ P)) (P ^ l) hE0 hPl0 hEi
    (integralMv_pow hP l) (by
      have := divByMv_neg hfc
      rwa [neg_sub] at this)
  have h4 : (desc l D).subst (P ^ l) =
      PowerSeries.subst P ((desc l D).subst ((X : PowerSeries K) ^ l) : PowerSeries K) := by
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hl0) hPs,
      PowerSeries.subst_pow hPs, PowerSeries.subst_X hPs]
  have h5 := divByMv_subst h1 hP0 hP
  rw [PowerSeries.subst_sub hPs, ← h4] at h5
  have := divByMv_sub h3 h5
  rwa [sub_sub_sub_cancel_right] at this

theorem desc_QCls (hF : FrobField K l σ) {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {b : K}
    (hΦ0 : MvPowerSeries.constantCoeff Φ = 0) (hΦ : IntegralMv Φ) (hA0 : constantCoeff A = 0)
    (hA : IntegralPS A) (hb : ‖b‖ ≤ 1) {D : PowerSeries K} (hD : QCls l Φ A b D)
    (hD' : DivBy (l : K) (PowerSeries.derivative D)) :
    QCls l (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) b (desc l D) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  refine ⟨by rw [desc_const, hD.D0], (desc_congr hF.prime hF.norm_l D hD').2, ?_, ?_⟩
  · rw [← divByMv_expand_iff _ l hl0, map_sub, map_sub]
    have h1 := desc_key hF hD.D0 hD' Φ hΦ0 hΦ
    have h2 := desc_key hF hD.D0 hD' (MvPowerSeries.X (0 : Fin 2)) (by simp) (integralMv_X _)
    have h3 := desc_key hF hD.D0 hD' (MvPowerSeries.X (1 : Fin 2)) (by simp) (integralMv_X _)
    rw [MvPowerSeries.map_X] at h2 h3
    have h4 := divByMv_add (divByMv_sub (divByMv_sub h1 h2) h3) hD.add
    convert h4 using 1
    simp only [atX, atY]
    ring
  · rw [divBy_iff_mv, ← divByMv_expand_iff _ l hl0, map_sub, map_mul]
    have h1 := desc_key hF hD.D0 hD' (ι := Unit) A hA0 ((integralPS_iff_mv A).1 hA)
    have h2 := desc_key hF hD.D0 hD' (ι := Unit) (X : PowerSeries K) (by simp [PowerSeries.X])
      ((integralPS_iff_mv _).1 integralPS_X)
    rw [show MvPowerSeries.map σ (X : PowerSeries K) = (X : PowerSeries K) from PowerSeries.map_X σ,
      PowerSeries.X_subst, PowerSeries.X_subst] at h2
    have h3 := divByMv_mul_left ((integralPS_iff_mv _).1 (integralPS_C hb)) h2
    have h4 := divByMv_add (divByMv_sub h1 h3) ((divBy_iff_mv _ _).1 hD.eig)
    have hC : MvPowerSeries.expand l hl0 (C b : PowerSeries K) = (C b : PowerSeries K) :=
      PowerSeries.expand_C l hl0 b
    rw [hC]
    convert h4 using 1
    simp only [PowerSeries.map]
    ring

end ReciprocityTheory.ChartRestriction.L1
