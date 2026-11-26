module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonC

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.DivByPartialYAtZeroSubstAtXAtY
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam₁ lam₂ : PowerSeries K} {Φ₁ Φ₂ : MvPowerSeries (Fin 2) K} {A₁ A₂ g : PowerSeries K}

theorem homE_coeff_one_subst {R : Type} [CommRing R] (f a : PowerSeries R) (ha : constantCoeff a = 0) :
    coeff 1 (f.subst a) = coeff 1 f * coeff 1 a := by
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero ha
  have hX : X ∣ a := X_dvd_iff.mpr ha
  rw [PowerSeries.coeff_subst' hs, finsum_eq_single _ 1]
  · simp [smul_eq_mul]
  · intro d hd
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · have : d = 0 := by omega
      subst this
      simp
    · have h2 : X ^ d ∣ a ^ d := pow_dvd_pow_of_dvd hX d
      have h3 := X_pow_dvd_iff.mp h2 1 h
      simp [h3]

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

theorem homE_norm_coeff_atX_mul_atY {x : K} (a b : PowerSeries K) (ha : IntegralPS a)
    (hb : ‖coeff 1 b‖ ≤ ‖x‖) (n : ℕ) :
    ‖MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 1) (atX a * atY b)‖ ≤ ‖x‖ := by
  unfold IntegralPS at ha
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_induction _ (fun y => ‖y‖ ≤ ‖x‖)
    (fun u v hu hv => (IsUltrametricDist.norm_add_le_max u v).trans (max_le hu hv))
    (by simp) fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  unfold atX atY
  rw [mvPowerSeries_coeff_subst_X_eq_ite_single, mvPowerSeries_coeff_subst_X_eq_ite_single]
  split_ifs with h1 h2
  · have e1 := congrArg (fun f => f 1) hp
    simp only [Finsupp.add_apply] at e1
    rw [h1] at e1
    simp at e1
    rw [norm_mul, e1]
    calc ‖coeff (p.1 0) a‖ * ‖coeff 1 b‖ ≤ 1 * ‖x‖ :=
          mul_le_mul (ha _) hb (norm_nonneg _) zero_le_one
      _ = ‖x‖ := one_mul _
  all_goals simp

theorem homE_norm_coeff_one_pow {x : K} (hg0 : constantCoeff g = 0) (h0 : ‖coeff 1 g‖ ≤ ‖x‖) (j : ℕ) :
    ‖coeff 1 (g ^ j)‖ ≤ ‖x‖ := by
  rcases j with _ | _ | j
  · simp
  · simpa using h0
  · have hX : X ∣ g := X_dvd_iff.mpr hg0
    have h2 := pow_dvd_pow_of_dvd hX (j + 1 + 1)
    rw [X_pow_dvd_iff.mp h2 1 (by omega), norm_zero]
    exact norm_nonneg _

theorem divBy_partialYAtZero_subst_atX_atY {x : K} (hΦ₂ : IntegralMv Φ₂) (hg0 : constantCoeff g = 0)
    (hg : IntegralPS g) (h0 : ‖coeff 1 g‖ ≤ ‖x‖) :
    DivBy x (d2 (Φ₂.subst ![atX g, atY g])) := by
  intro n
  have hX : PowerSeries.HasSubst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.X 0
  have hY : PowerSeries.HasSubst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.X 1
  have hP' : MvPowerSeries.HasSubst ![atX g, atY g] := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => ?_
    fin_cases i
    · exact PowerSeries.constantCoeff_subst_eq_zero (by simp) g hg0
    · exact PowerSeries.constantCoeff_subst_eq_zero (by simp) g hg0
  rw [d2, coeff_mk, MvPowerSeries.coeff_subst hP']
  refine Formalism.LT.LTL.norm_finsum_le' (norm_nonneg _) fun m => ?_
  rw [smul_eq_mul, norm_mul, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [atX, atY, ← PowerSeries.subst_pow hX, ← PowerSeries.subst_pow hY]
  have := homE_norm_coeff_atX_mul_atY (g ^ m 0) (g ^ m 1) (integralPS_pow hg _)
    (homE_norm_coeff_one_pow hg0 h0 _) n
  exact (mul_le_mul (hΦ₂ m) this (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem hom_deriv (hl1 : ‖(l : K)‖ ≤ 1) (h₁ : LawD lam₁ Φ₁) (h₂ : LawD lam₂ Φ₂)
    (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g) (h0 : ‖coeff 1 g‖ ≤ ‖(l : K)‖) :
    DivBy (l : K) (derivative g) := by
  have hchain (D : PowerSeries K) : d2 (D.subst Φ₁) = derivative D * d2 Φ₁ := by
    rw [partialYAtZero_eq, Formalism.G.LogCR.pderiv_psubst h₁.Φ0, evalYZero_mul,
      evalYZero_subst _ h₁.Φ0, h₁.evalYZero_eq, PowerSeries.X_subst, ← partialYAtZero_eq]
  have h1 := divBy_partialYAtZero hg.add
  rw [partialYAtZero_sub, hchain] at h1
  have h2 := divBy_partialYAtZero_subst_atX_atY (x := (l : K)) h₂.Φint hg.g0 hg.gInt h0
  have h3 : DivBy (l : K) (derivative g * d2 Φ₁) := by
    unfold DivBy at h1 h2 ⊢
    intro n
    have h4 := IsUltrametricDist.norm_add_le_max
      (coeff n (derivative g * d2 Φ₁ - d2 (Φ₂.subst ![atX g, atY g])))
      (coeff n (d2 (Φ₂.subst ![atX g, atY g])))
    rw [← map_add (f := _), sub_add_cancel] at h4
    exact h4.trans (max_le (h1 n) (h2 n))
  have hunit : constantCoeff (d2 Φ₁) = 1 := by
    have hmul : derivative lam₁ * d2 Φ₁ = 1 := by
      have hlog := congrArg d2 h₁.log
      rwa [hchain, partialYAtZero_add, partialYAtZero_atX, partialYAtZero_atY,
        h₁.lam1, zero_add, map_one] at hlog
    have hconst : constantCoeff (derivative lam₁) = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
      simp [h₁.lam1]
    have h := congrArg constantCoeff hmul
    rwa [map_mul, hconst, one_mul, map_one] at h
  exact divBy_of_mul_unit (integralPS_partialYAtZero h₁.Φint) (by rw [hunit, norm_one])
    (by simpa only [mul_comm] using h3)

theorem hom_eigen (hA₁ : constantCoeff A₁ = 0) (hA₂ : constantCoeff A₂ = 0)
    (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g) (h : ‖coeff 1 A₁ - coeff 1 A₂‖ = 1) :
    ‖coeff 1 g‖ ≤ ‖(l : K)‖ := by
  have h0 := hg.eig
  unfold DivBy at h0
  have h1 := h0 1
  have e : coeff 1 g * coeff 1 A₁ - coeff 1 A₂ * coeff 1 g =
      coeff 1 g * (coeff 1 A₁ - coeff 1 A₂) := by ring
  rw [map_sub, homE_coeff_one_subst _ _ hA₁, homE_coeff_one_subst _ _ hg.g0, e, norm_mul, h,
    mul_one] at h1
  exact h1

theorem homE_expand_subst_map_congr {ι : Type} (hF : FrobField K l σ) {g₁ : PowerSeries K}
    (hg₁ : IntegralPS g₁) (hc : DivBy (l : K) (g - g₁.subst ((X : PowerSeries K) ^ l)))
    (P : MvPowerSeries ι K) (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv (l : K) (MvPowerSeries.expand l hF.prime.ne_zero (g₁.subst (MvPowerSeries.map σ P))
      - g.subst P) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  have hσ0 : MvPowerSeries.constantCoeff (MvPowerSeries.map σ P) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hP0, map_zero]
  have hs : PowerSeries.HasSubst (MvPowerSeries.map σ P) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hσ0
  have hPs : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  rw [PowerSeries.expand_subst l hl0 hs g₁]
  have hfr := Formalism.LT.FrobCongr_valid K l l hl0 σ hF.funEqSetting ι P hP
  have T1 : DivByMv (l : K) (g₁.subst (MvPowerSeries.expand l hl0 (MvPowerSeries.map σ P))
      - g₁.subst (P ^ l)) := by
    refine divByMv_subst_congr hF.norm_l.le hg₁ ?_ ?_ ?_ (integralMv_pow hP l) ?_
    · rw [MvPowerSeries.constantCoeff_expand, hσ0]
    · rw [map_pow, hP0, zero_pow hl0]
    · exact (integralMv_iff_divBy_one _).2 ((divByMv_expand_iff 1 l hl0 _).2
        ((integralMv_iff_divBy_one _).1 (hF.integralMv_map hP)))
    · rw [← neg_sub]; exact divByMv_neg hfr
  have T2 : g₁.subst (P ^ l) = PowerSeries.subst P (g₁.subst ((X : PowerSeries K) ^ l) : PowerSeries K) := by
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hl0) hPs,
      PowerSeries.subst_pow hPs, PowerSeries.subst_X hPs]
  have T3 : DivByMv (l : K) (PowerSeries.subst P (g₁.subst ((X : PowerSeries K) ^ l) : PowerSeries K) - g.subst P) := by
    rw [← PowerSeries.subst_sub hPs]
    refine divByMv_subst ?_ hP0 hP
    rw [← neg_sub]; exact divBy_neg hc
  rw [T2] at T1
  have := divByMv_add T1 T3
  rwa [sub_add_sub_cancel] at this

theorem homE_vec_const {f : PowerSeries K} (hf0 : constantCoeff f = 0) (i : Fin 2) :
    MvPowerSeries.constantCoeff (![atX f, atY f] i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  fin_cases i <;> simp [atX, atY, mvPowerSeries_coeff_subst_X_eq_ite_single, hf0]

theorem homE_vec_integral {f : PowerSeries K} (hf : IntegralPS f) (i : Fin 2) :
    IntegralMv (![atX f, atY f] i) := by
  unfold IntegralPS at hf
  unfold IntegralMv
  intro e
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, atX, atY, mvPowerSeries_coeff_subst_X_eq_ite_single]
  all_goals split_ifs
  all_goals first | exact hf _ | simp

theorem homE_vec_divBy {x : K} {f h : PowerSeries K} (hfh : DivBy x (f - h)) (i : Fin 2) :
    DivByMv x (![atX f, atY f] i - ![atX h, atY h] i) := by
  unfold DivBy at hfh
  unfold DivByMv
  intro e
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, atX, atY, map_sub, mvPowerSeries_coeff_subst_X_eq_ite_single]
  all_goals split_ifs
  all_goals first | (rw [← map_sub]; exact hfh _) | simp

theorem homE_expand_subst_X (hl0 : l ≠ 0) (f : PowerSeries K) (i : Fin 2) :
    MvPowerSeries.expand l hl0 (f.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K)) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K)
        (f.subst ((X : PowerSeries K) ^ l) : PowerSeries K) := by
  rw [PowerSeries.expand_subst l hl0 (PowerSeries.HasSubst.X i), MvPowerSeries.expand_X,
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hl0) (PowerSeries.HasSubst.X i),
    PowerSeries.subst_pow (PowerSeries.HasSubst.X i), PowerSeries.subst_X (PowerSeries.HasSubst.X i)]

theorem hom_desc (hF : FrobField K l σ) (hΦ₁0 : MvPowerSeries.constantCoeff Φ₁ = 0)
    (hΦ₁ : IntegralMv Φ₁) (hΦ₂0 : MvPowerSeries.constantCoeff Φ₂ = 0) (hΦ₂ : IntegralMv Φ₂)
    (hA₁0 : constantCoeff A₁ = 0) (hA₁ : IntegralPS A₁) (hA₂0 : constantCoeff A₂ = 0)
    (hA₂ : IntegralPS A₂) (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g) (hg' : DivBy (l : K) (derivative g)) :
    DivBy (l : K) (g - (desc l g).subst ((X : PowerSeries K) ^ l)) ∧
      HomCls l (MvPowerSeries.map σ Φ₁) (PowerSeries.map σ A₁) Φ₂ A₂ (desc l g) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  have hc : DivBy (l : K) (g - (desc l g).subst ((X : PowerSeries K) ^ l)) := by
    intro m
    rw [map_sub, PowerSeries.coeff_subst_X_pow hl0, Algebra.algebraMap_self, RingHom.id_apply]
    split_ifs with hm
    · obtain ⟨q, rfl⟩ := hm
      rw [desc, coeff_mk, Nat.mul_div_cancel_left q hF.prime.pos, sub_self, norm_zero]
      exact norm_nonneg _
    · rw [sub_zero]
      have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero l)
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have h := hg' n
      rwa [coeff_derivative, norm_mul, ← Nat.cast_add_one,
        norm_natCast_of_coprime hF.prime hF.norm_l _ hm, mul_one] at h
  refine ⟨hc, ?_⟩
  have hg₁0 : constantCoeff (desc l g) = 0 := by rw [desc_const, hg.g0]
  have hg₁ : IntegralPS (desc l g) := desc_integral hg.gInt
  generalize desc l g = g₁ at hc hg₁0 hg₁ ⊢
  obtain ⟨E, hE⟩ : ∃ E : PowerSeries K, E = g₁.subst ((X : PowerSeries K) ^ l) := ⟨_, rfl⟩
  have hE0 : constantCoeff E = 0 := by
    rw [hE]; exact PowerSeries.constantCoeff_subst_eq_zero
      (by rw [map_pow]; exact (congrArg (· ^ l) (constantCoeff_X (R := K))).trans (zero_pow hl0)) g₁ hg₁0
  have hEint : IntegralPS E := by
    rw [hE]
    exact (integralPS_iff_divBy_one _).2 ((divBy_expand_iff 1 l hl0 g₁).2
      ((integralPS_iff_divBy_one _).1 hg₁))
  have hc' : DivBy (l : K) (g - E) := by rw [hE]; exact hc
  refine ⟨hg₁0, hg₁, ?_, ?_⟩
  · rw [← divByMv_expand_iff (l : K) l hl0, map_sub]
    have T := homE_expand_subst_map_congr hF hg₁ hc Φ₁ hΦ₁0 hΦ₁
    have hv : MvPowerSeries.HasSubst ![atX g₁, atY g₁] :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (homE_vec_const hg₁0)
    have hex : MvPowerSeries.expand l hl0 (Φ₂.subst ![atX g₁, atY g₁]) =
        Φ₂.subst ![atX E, atY E] := by
      rw [MvPowerSeries.expand_subst l hl0 hv]
      congr 1
      funext i
      fin_cases i
      · show MvPowerSeries.expand l hl0 (atX g₁) = atX E
        rw [atX, atX, homE_expand_subst_X hl0, hE]
      · show MvPowerSeries.expand l hl0 (atY g₁) = atY E
        rw [atY, atY, homE_expand_subst_X hl0, hE]
    have T5 : DivByMv (l : K) (Φ₂.subst ![atX g, atY g] - Φ₂.subst ![atX E, atY E]) :=
      divByMv_subst2_congr hF.norm_l.le hΦ₂ (homE_vec_const hg.g0) (homE_vec_const hE0)
        (homE_vec_integral hg.gInt) (homE_vec_integral hEint) (homE_vec_divBy hc')
    rw [hex]
    have := divByMv_add (divByMv_add T hg.add) T5
    rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this
  · rw [divBy_iff_mv, ← divByMv_expand_iff (l : K) l hl0, map_sub]
    have T := homE_expand_subst_map_congr (ι := Unit) hF hg₁ hc A₁ hA₁0 ((integralPS_iff_mv _).1 hA₁)
    have hex : MvPowerSeries.expand l hl0 (A₂.subst g₁) = A₂.subst E := by
      rw [PowerSeries.expand_subst l hl0 (PowerSeries.HasSubst.of_constantCoeff_zero' hg₁0), hE]
      congr 1
      exact PowerSeries.expand_apply l hl0 g₁
    have T5 : DivByMv (l : K) (A₂.subst g - A₂.subst E) :=
      divByMv_subst_congr (ι := Unit) hF.norm_l.le hA₂ hg.g0 hE0 ((integralPS_iff_mv _).1 hg.gInt)
        ((integralPS_iff_mv _).1 hEint) ((divBy_iff_mv _ _).1 hc')
    rw [hex]
    have := divByMv_add (divByMv_add T ((divBy_iff_mv _ _).1 hg.eig)) T5
    rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonD
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Tools

variable {R : Type} [CommRing R]

theorem coeffOne_subst_zero {f s : PowerSeries R} (hs : constantCoeff s = 0) :
    coeff 1 (f.subst s) = coeff 1 f * coeff 1 s := by
  have ha : HasSubst s := HasSubst.of_constantCoeff_zero hs
  have hX : X ∣ s := X_dvd_iff.mpr hs
  rw [PowerSeries.coeff_subst' ha, finsum_eq_single _ 1]
  · simp [smul_eq_mul]
  · intro d hd
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · have : d = 0 := by omega
      subst this
      simp
    · have h2 : X ^ d ∣ s ^ d := pow_dvd_pow_of_dvd hX d
      have h3 := X_pow_dvd_iff.mp h2 1 h
      simp [h3]

theorem subst_C_mul_mv {ι : Type} {P : MvPowerSeries ι R} (hP : HasSubst P) (c : R)
    (f : PowerSeries R) : (C c * f).subst P = MvPowerSeries.C c * f.subst P := by
  rw [← smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, ← coe_substAlgHom hP, map_smul]

theorem subst_C_mul_ps {P : PowerSeries R} (hP : HasSubst P) (c : R)
    (f : PowerSeries R) : (C c * f).subst P = C c * f.subst P := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, ← coe_substAlgHom hP, map_smul]

end Tools

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem LawD.map (hF : FrobField K l σ) (h : LawD lam Φ) :
    LawD (PowerSeries.map σ lam) (MvPowerSeries.map σ Φ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.lam0,
      map_zero]
  · rw [coeff_map, h.lam1, map_one]
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, map_zero]
  · have h1 := h.Φint
    unfold IntegralMv at h1 ⊢
    intro e
    rw [MvPowerSeries.coeff_map, hF.isom]
    exact h1 e
  · have h1 := congrArg (MvPowerSeries.map σ) h.log
    unfold atX atY at h1 ⊢
    rw [map_add (f := _)] at h1
    erw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero h.Φ0),
      PowerSeries.map_subst (HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)),
      PowerSeries.map_subst (HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)),
      MvPowerSeries.map_X, MvPowerSeries.map_X] at h1
    exact h1

theorem HD.map (hF : FrobField K l σ) (h : HD σ lam Φ A a) :
    HD σ (PowerSeries.map σ lam) (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) (σ a) := by
  refine ⟨h.toLawD.map hF, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.A0,
      map_zero]
  · have h1 := h.Aint
    unfold IntegralPS at h1 ⊢
    intro n
    rw [coeff_map, hF.isom]
    exact h1 n
  · have h1 := congrArg (PowerSeries.map σ) h.Alog
    erw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero h.A0)] at h1
    rw [map_mul, map_C] at h1
    exact h1
  · rw [h.a_sq, norm_sub_rev]
    exact h.a_ne
  · rw [h.a_sq]

theorem HD.coeff_one_A (h : HD σ lam Φ A a) : coeff 1 A = a := by
  have h1 := congrArg (coeff 1) h.Alog
  rw [coeffOne_subst_zero h.A0, coeff_C_mul, h.lam1, one_mul, mul_one] at h1
  exact h1

theorem HD.norm_a (h : HD σ lam Φ A a) : ‖a‖ ≤ 1 := by
  have h1 := h.Aint
  unfold IntegralPS at h1
  rw [← h.coeff_one_A]
  exact h1 1

theorem eigen_trick {A : PowerSeries K} {b : K} (hA0 : constantCoeff A = 0) (D : PowerSeries K)
    (hD0 : constantCoeff D = 0) (h : DivBy (l : K) (D.subst A - C b * D))
    (hb : ‖coeff 1 A - b‖ = 1) : ‖coeff 1 D‖ ≤ ‖(l : K)‖ := by
  have h0 := h
  unfold DivBy at h0
  have h1 := h0 1
  have e : coeff 1 D * coeff 1 A - b * coeff 1 D = coeff 1 D * (coeff 1 A - b) := by ring
  rw [map_sub, coeffOne_subst_zero hA0, coeff_C_mul, e, norm_mul, hb, mul_one] at h1
  exact h1

theorem divBy_C_mul' {x c : K} (hc : ‖c‖ ≤ ‖x‖) {f : PowerSeries K} (hf : IntegralPS f) :
    DivBy x (C c * f) := by
  unfold DivBy IntegralPS at *
  intro n
  rw [coeff_C_mul, norm_mul]
  calc ‖c‖ * ‖coeff n f‖ ≤ ‖x‖ * 1 := mul_le_mul hc (hf n) (norm_nonneg _) (norm_nonneg _)
    _ = ‖x‖ := mul_one _

theorem derivative_C_mul' (c : K) (f : PowerSeries K) :
    PowerSeries.derivative (C c * f) = C c * PowerSeries.derivative f := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, Derivation.map_smul]

theorem QCls.norm_coeff_one {b : K} {D : PowerSeries K} (hD : QCls l Φ A b D) :
    ‖coeff 1 D‖ ≤ 1 := by
  have h0 := hD.dInt
  unfold IntegralPS at h0
  have h1 := h0 0
  rw [coeff_derivative] at h1
  simpa using h1

theorem HD.qcls_sub (h : HD σ lam Φ A a) {D : PowerSeries K} (hD : QCls l Φ A a D) :
    QCls l Φ A a (D - C (coeff 1 D) * lam) := by
  set c := coeff 1 D with hc
  have hc1 : ‖c‖ ≤ 1 := hD.norm_coeff_one
  have hΦ : HasSubst Φ := HasSubst.of_constantCoeff_zero h.Φ0
  have hA : HasSubst A := HasSubst.of_constantCoeff_zero h.A0
  have hX0 : HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) :=
    HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)
  have hX1 : HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) :=
    HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)
  have sub_subst : ∀ {P : MvPowerSeries (Fin 2) K} (_ : HasSubst P) (f g : PowerSeries K),
      (f - g).subst P = f.subst P - g.subst P := fun hP f g => by
    rw [← coe_substAlgHom hP, map_sub]
  have sub_substA : (D - C c * lam).subst A = D.subst A - C c * lam.subst A := by
    rw [← coe_substAlgHom hA, map_sub, coe_substAlgHom hA, subst_C_mul_ps hA]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hD.D0, h.lam0]
  · have hd := hD.dInt
    have hl := h.toLawD.deriv_integral
    unfold IntegralPS at hd hl ⊢
    intro n
    rw [map_sub, derivative_C_mul', map_sub, coeff_C_mul, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hd n) ?_)
    rw [norm_neg, norm_mul]
    calc ‖c‖ * ‖coeff n (PowerSeries.derivative lam)‖ ≤ 1 * 1 :=
          mul_le_mul hc1 (hl n) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have e : (D - C c * lam).subst Φ - atX (D - C c * lam) - atY (D - C c * lam) =
        (D.subst Φ - atX D - atY D) - MvPowerSeries.C c * (lam.subst Φ - atX lam - atY lam) := by
      unfold atX atY
      rw [sub_subst hΦ, sub_subst hX0, sub_subst hX1, subst_C_mul_mv hΦ, subst_C_mul_mv hX0,
        subst_C_mul_mv hX1]
      ring
    have e2 : lam.subst Φ - atX lam - atY lam = 0 := by rw [h.log]; ring
    rw [e, e2, mul_zero, sub_zero]
    exact hD.add
  · have e : (D - C c * lam).subst A - C a * (D - C c * lam) = D.subst A - C a * D := by
      rw [sub_substA, h.Alog]
      ring
    rw [e]
    exact hD.eig

theorem lemmaQ (hF : FrobField K l σ) (h : HD σ lam Φ A a) {D : PowerSeries K}
    (hD : QCls l Φ A a D) :
    ∃ Dp : PowerSeries K,
      QCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) a Dp ∧
      DivBy (l : K) (D - C (coeff 1 D) * lam - Dp.subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  set E : PowerSeries K := D - C (coeff 1 D) * lam with hE
  have hEq : QCls l Φ A a E := h.qcls_sub hD
  have hE' : DivBy (l : K) (PowerSeries.derivative E) := by
    have := hon_deriv h.toLawD (l : K) D hD.add
    rwa [hE, map_sub, derivative_C_mul']
  have h1 : QCls l (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) a (desc l E) :=
    desc_QCls hF h.Φ0 h.Φint h.A0 h.Aint h.norm_a hEq hE'
  have c1 := (desc_congr hF.prime hF.norm_l E hE').1
  have hσ := h.map hF
  have hs : ‖coeff 1 (desc l E)‖ ≤ ‖(l : K)‖ :=
    eigen_trick hσ.A0 _ h1.D0 h1.eig (by rw [hσ.coeff_one_A]; exact h.a_ne)
  have h1' : DivBy (l : K) (PowerSeries.derivative (desc l E)) := by
    have h2 := hon_deriv hσ.toLawD (l : K) _ h1.add
    have h3 := divBy_add h2 (divBy_C_mul' hs hσ.toLawD.deriv_integral)
    rwa [sub_add_cancel] at h3
  have h2 : QCls l (MvPowerSeries.map σ (MvPowerSeries.map σ Φ))
      (PowerSeries.map σ (PowerSeries.map σ A)) a (desc l (desc l E)) :=
    desc_QCls hF hσ.Φ0 hσ.Φint hσ.A0 hσ.Aint h.norm_a h1 h1'
  have c2 := (desc_congr hF.prime hF.norm_l _ h1').1
  refine ⟨desc l (desc l E), ?_, ?_⟩
  · have e1 : MvPowerSeries.map (σ.comp σ) Φ = MvPowerSeries.map σ (MvPowerSeries.map σ Φ) := by
      ext d; simp
    have e2 : PowerSeries.map (σ.comp σ) A = PowerSeries.map σ (PowerSeries.map σ A) := by
      ext d; simp
    rw [e1, e2]; exact h2
  · have hXl : HasSubst ((X : PowerSeries K) ^ l) :=
      HasSubst.of_constantCoeff_zero' (by simp [hl0])
    have c3 := (divBy_expand_iff (l : K) l hl0 _).2 c2
    rw [subst_sub hXl, subst_comp_subst_apply hXl hXl, subst_pow hXl, subst_X hXl, ← pow_mul,
      ← sq] at c3
    have c4 := divBy_add c1 c3
    rwa [sub_add_sub_cancel] at c4

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem LawD.subst_of_log (h : LawD lam Φ) {e : PowerSeries K} {c : K} (he0 : constantCoeff e = 0)
    (hlog : lam.subst e = C c * lam) : e.subst Φ = Φ.subst ![atX e, atY e] := by
  have hes : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have hΦs : PowerSeries.HasSubst Φ := PowerSeries.HasSubst.of_constantCoeff_zero h.Φ0
  have hlog' : lam.subst e = c • lam := by rw [hlog, smul_eq_C_mul]
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have hx0 : MvPowerSeries.constantCoeff (atX e) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ he0
  have hy0 : MvPowerSeries.constantCoeff (atY e) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ he0
  have hb : MvPowerSeries.HasSubst ![atX e, atY e] := Formalism.G.LogP.hs2 hx0 hy0
  have hb0 : ∀ i, MvPowerSeries.constantCoeff (![atX e, atY e] i) = 0 := by
    intro i; fin_cases i <;> simpa
  refine Formalism.G.LogP.psubst_injective h.lam0 h.lam1
    (PowerSeries.constantCoeff_subst_eq_zero h.Φ0 _ he0)
    (MvPowerSeries.constantCoeff_subst_eq_zero hb hb0 h.Φ0) ?_
  rw [← PowerSeries.subst_comp_subst_apply hes hΦs, hlog', PowerSeries.subst_smul hΦs, h.log,
    ← Formalism.G.LogP.psubst_subst lam h.Φ0 hb, h.log, MvPowerSeries.subst_add hb,
    Formalism.G.LogP.psubst_subst lam (MvPowerSeries.constantCoeff_X _) hb,
    Formalism.G.LogP.psubst_subst lam (MvPowerSeries.constantCoeff_X _) hb,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
  show _ = lam.subst (e.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K))
    + lam.subst (e.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K))
  rw [← PowerSeries.subst_comp_subst_apply hes (hX 0), ← PowerSeries.subst_comp_subst_apply hes (hX 1),
    hlog', PowerSeries.subst_smul (hX 0), PowerSeries.subst_smul (hX 1), smul_add]

theorem LawD.comm_of_log (h : LawD lam Φ) {e f : PowerSeries K} {c d : K}
    (he0 : constantCoeff e = 0) (hf0 : constantCoeff f = 0)
    (hlog : lam.subst e = C c * lam) (hlogf : lam.subst f = C d * lam) :
    e.subst f = f.subst e := by
  have hes : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hlog' : lam.subst e = c • lam := by rw [hlog, smul_eq_C_mul]
  have hlogf' : lam.subst f = d • lam := by rw [hlogf, smul_eq_C_mul]
  refine Formalism.G.LogP.psubst_injective (σ := Unit) h.lam0 h.lam1
    (PowerSeries.constantCoeff_subst_eq_zero hf0 _ he0)
    (PowerSeries.constantCoeff_subst_eq_zero he0 _ hf0) ?_
  rw [← PowerSeries.subst_comp_subst_apply hes hfs, ← PowerSeries.subst_comp_subst_apply hfs hes,
    hlog', hlogf', PowerSeries.subst_smul hfs, PowerSeries.subst_smul hes, hlog', hlogf',
    smul_smul, smul_smul, mul_comm]

theorem mulL_homCls (h : HD σ lam Φ A a) {e : PowerSeries K} (he0 : constantCoeff e = 0)
    (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) : HomCls l Φ A Φ A e := by
  refine ⟨he0, he, ?_, ?_⟩
  · rw [h.toLawD.subst_of_log he0 hlog, sub_self]
    exact divByMv_zero _
  · rw [h.toLawD.comm_of_log he0 h.A0 hlog h.Alog, sub_self]
    intro n
    simp

theorem mulL_deriv (h : LawD lam Φ) {e : PowerSeries K} (he0 : constantCoeff e = 0)
    (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) :
    DivBy (l : K) (derivative e) := by
  have hconst : constantCoeff (derivative lam) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
    simp [h.lam1]
  have hmul : derivative lam * d2 Φ = 1 := by
    have hchain : d2 (lam.subst Φ) = derivative lam * d2 Φ := by
      rw [partialYAtZero_eq, Formalism.G.LogCR.pderiv_psubst h.Φ0, evalYZero_mul,
        evalYZero_subst _ h.Φ0, h.evalYZero_eq, PowerSeries.X_subst, ← partialYAtZero_eq]
    have hlogD := congrArg d2 h.log
    rwa [hchain, partialYAtZero_add, partialYAtZero_atX, partialYAtZero_atY,
      h.lam1, zero_add, map_one] at hlogD
  have hunit : constantCoeff (d2 Φ) = 1 := by
    have hcoeff := congrArg constantCoeff hmul
    rwa [map_mul, hconst, one_mul, map_one] at hcoeff
  have hIntegral : IntegralPS (derivative lam) := by
    rw [integralPS_iff_divBy_one]
    refine divBy_of_mul_unit (integralPS_partialYAtZero h.Φint) (by rw [hunit, norm_one]) ?_
    rw [mul_comm, hmul]
    intro n
    by_cases hn : n = 0 <;> simp [coeff_one, hn]
  have hes : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have h1 : (derivative lam).subst e * derivative e = C (l : K) * derivative lam := by
    rw [← PowerSeries.derivative_subst hes, hlog]
    simp
  have hi : IntegralPS ((derivative lam).subst e) :=
    (integralPS_iff_mv _).2 (integralMv_subst hIntegral he0 ((integralPS_iff_mv _).1 he))
  have hc : constantCoeff ((derivative lam).subst e) = 1 := by
    exact (PowerSeries.constantCoeff_subst_of_constantCoeff_zero he0 (derivative lam)).trans hconst
  refine divBy_of_mul_unit hi (by rw [hc, norm_one]) ?_
  rw [h1]
  intro n
  rw [coeff_C_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hIntegral n)

theorem hon_shape (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) :
    ∃ hh : PowerSeries K,
      HomCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) Φ A hh ∧
      DivBy (l : K) (e - hh.subst ((X : PowerSeries K) ^ (l ^ 2))) ∧
      coeff 1 hh = coeff (l ^ 2) e := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  have descend {Φ₁ Φ₂ : MvPowerSeries (Fin 2) K} {A₁ A₂ g : PowerSeries K}
      (hΦ₁0 : MvPowerSeries.constantCoeff Φ₁ = 0) (hΦ₁ : IntegralMv Φ₁)
      (hΦ₂ : IntegralMv Φ₂) (hA₁0 : constantCoeff A₁ = 0)
      (hA₁ : IntegralPS A₁) (hA₂ : IntegralPS A₂) (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g)
      (hg' : DivBy (l : K) (derivative g)) :
      DivBy (l : K) (g - (desc l g).subst ((X : PowerSeries K) ^ l)) ∧
        HomCls l (MvPowerSeries.map σ Φ₁) (PowerSeries.map σ A₁) Φ₂ A₂ (desc l g) := by
    have hc : DivBy (l : K) (g - (desc l g).subst ((X : PowerSeries K) ^ l)) := by
      intro m
      rw [map_sub, PowerSeries.coeff_subst_X_pow hl0, Algebra.algebraMap_self, RingHom.id_apply]
      split_ifs with hm
      · obtain ⟨q, rfl⟩ := hm
        rw [desc, coeff_mk, Nat.mul_div_cancel_left q hF.prime.pos, sub_self, norm_zero]
        exact norm_nonneg _
      · rw [sub_zero]
        have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero l)
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
        have h := hg' n
        rwa [coeff_derivative, norm_mul, ← Nat.cast_add_one,
          norm_natCast_of_coprime hF.prime hF.norm_l _ hm, mul_one] at h
    refine ⟨hc, ?_⟩
    have hg₁0 : constantCoeff (desc l g) = 0 := by rw [desc_const, hg.g0]
    have hg₁ : IntegralPS (desc l g) := desc_integral hg.gInt
    generalize desc l g = g₁ at hc hg₁0 hg₁ ⊢
    obtain ⟨E, hE⟩ : ∃ E : PowerSeries K, E = g₁.subst ((X : PowerSeries K) ^ l) := ⟨_, rfl⟩
    have hE0 : constantCoeff E = 0 := by
      rw [hE]
      refine PowerSeries.constantCoeff_subst_eq_zero ?_ g₁ hg₁0
      rw [map_pow]
      exact (congrArg (· ^ l) (constantCoeff_X (R := K))).trans (zero_pow hl0)
    have hEint : IntegralPS E := by
      rw [hE]
      exact (integralPS_iff_divBy_one _).2 ((divBy_expand_iff 1 l hl0 g₁).2
        ((integralPS_iff_divBy_one _).1 hg₁))
    have hc' : DivBy (l : K) (g - E) := by rw [hE]; exact hc
    refine ⟨hg₁0, hg₁, ?_, ?_⟩
    · rw [← divByMv_expand_iff (l : K) l hl0, map_sub]
      have T := homE_expand_subst_map_congr hF hg₁ hc Φ₁ hΦ₁0 hΦ₁
      have hv : MvPowerSeries.HasSubst ![atX g₁, atY g₁] :=
        MvPowerSeries.hasSubst_of_constantCoeff_zero (homE_vec_const hg₁0)
      have hex : MvPowerSeries.expand l hl0 (Φ₂.subst ![atX g₁, atY g₁]) =
          Φ₂.subst ![atX E, atY E] := by
        rw [MvPowerSeries.expand_subst l hl0 hv]
        congr 1
        funext i
        fin_cases i
        · show MvPowerSeries.expand l hl0 (atX g₁) = atX E
          rw [atX, atX, homE_expand_subst_X hl0, hE]
        · show MvPowerSeries.expand l hl0 (atY g₁) = atY E
          rw [atY, atY, homE_expand_subst_X hl0, hE]
      have T5 : DivByMv (l : K) (Φ₂.subst ![atX g, atY g] - Φ₂.subst ![atX E, atY E]) :=
        divByMv_subst2_congr hF.norm_l.le hΦ₂ (homE_vec_const hg.g0) (homE_vec_const hE0)
          (homE_vec_integral hg.gInt) (homE_vec_integral hEint) (homE_vec_divBy hc')
      rw [hex]
      have := divByMv_add (divByMv_add T hg.add) T5
      rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this
    · rw [divBy_iff_mv, ← divByMv_expand_iff (l : K) l hl0, map_sub]
      have T := homE_expand_subst_map_congr (ι := Unit) hF hg₁ hc A₁ hA₁0 ((integralPS_iff_mv _).1 hA₁)
      have hex : MvPowerSeries.expand l hl0 (A₂.subst g₁) = A₂.subst E := by
        rw [PowerSeries.expand_subst l hl0 (PowerSeries.HasSubst.of_constantCoeff_zero' hg₁0), hE]
        congr 1
        exact PowerSeries.expand_apply l hl0 g₁
      have T5 : DivByMv (l : K) (A₂.subst g - A₂.subst E) :=
        divByMv_subst_congr (ι := Unit) hF.norm_l.le hA₂ hg.g0 hE0 ((integralPS_iff_mv _).1 hg.gInt)
          ((integralPS_iff_mv _).1 hEint) ((divBy_iff_mv _ _).1 hc')
      rw [hex]
      have := divByMv_add (divByMv_add T ((divBy_iff_mv _ _).1 hg.eig)) T5
      rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this
  have hσ := h.map hF
  obtain ⟨hc1, hH1⟩ := descend h.Φ0 h.Φint h.Φint h.A0 h.Aint h.Aint
    (mulL_homCls h he0 he hlog) (mulL_deriv h.toLawD he0 he hlog)
  have hsmall : ‖coeff 1 (desc l e)‖ ≤ ‖(l : K)‖ := by
    refine hom_eigen hσ.A0 h.A0 hH1 ?_
    rw [hσ.coeff_one_A, h.coeff_one_A]
    exact h.a_ne
  have hd1 : DivBy (l : K) (derivative (desc l e)) := by
    let Φσ := MvPowerSeries.map σ Φ
    have hchain (D : PowerSeries K) : d2 (D.subst Φσ) = derivative D * d2 Φσ := by
      rw [partialYAtZero_eq, Formalism.G.LogCR.pderiv_psubst hσ.Φ0, evalYZero_mul,
        evalYZero_subst _ hσ.Φ0, hσ.toLawD.evalYZero_eq, PowerSeries.X_subst, ← partialYAtZero_eq]
    have hadd := divBy_partialYAtZero hH1.add
    rw [partialYAtZero_sub, hchain] at hadd
    have hsubst := divBy_partialYAtZero_subst_atX_atY h.Φint hH1.g0 hH1.gInt hsmall
    have hprod : DivBy (l : K) (derivative (desc l e) * d2 Φσ) := by
      simpa only [sub_add_cancel] using divBy_add hadd hsubst
    have hmul : derivative (PowerSeries.map σ lam) * d2 Φσ = 1 := by
      have hlogD := congrArg d2 hσ.log
      rwa [hchain, partialYAtZero_add, partialYAtZero_atX, partialYAtZero_atY,
        hσ.lam1, zero_add, map_one] at hlogD
    have hconst : constantCoeff (derivative (PowerSeries.map σ lam)) = 1 := by
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
      simp [hσ.lam1]
    have hunit : constantCoeff (d2 Φσ) = 1 := by
      have hcoeff := congrArg constantCoeff hmul
      rwa [map_mul, hconst, one_mul, map_one] at hcoeff
    exact divBy_of_mul_unit (integralPS_partialYAtZero hσ.Φint) (by rw [hunit, norm_one])
      (by rwa [mul_comm])
  obtain ⟨hc2, hH2⟩ := descend hσ.Φ0 hσ.Φint h.Φint hσ.A0 hσ.Aint h.Aint hH1 hd1
  refine ⟨desc l (desc l e), ?_, ?_, ?_⟩
  · have e1 : MvPowerSeries.map (σ.comp σ) Φ = MvPowerSeries.map σ (MvPowerSeries.map σ Φ) := by
      ext d; simp
    have e2 : PowerSeries.map (σ.comp σ) A = PowerSeries.map σ (PowerSeries.map σ A) := by
      ext d; simp
    rw [e1, e2]
    exact hH2
  · have hXs : PowerSeries.HasSubst ((X : PowerSeries K) ^ l) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl0])
    have h3 := (divBy_expand_iff (l : K) l hl0 _).2 hc2
    rw [PowerSeries.subst_sub hXs, PowerSeries.subst_comp_subst_apply hXs hXs,
      PowerSeries.subst_pow hXs, PowerSeries.subst_X hXs, ← pow_mul, ← sq] at h3
    have h4 := divBy_add hc1 h3
    rwa [sub_add_sub_cancel] at h4
  · rw [coeff_one_desc, desc, coeff_mk, sq]

theorem hon_level (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) : ‖coeff (l ^ 2) e‖ = 1 := by
  obtain ⟨hh, -, hc, -⟩ := hon_shape hF h he0 he hlog
  obtain ⟨i, hi, hi1⟩ := hlev
  have hq0 : l ^ 2 ≠ 0 := pow_ne_zero _ hF.prime.ne_zero
  by_cases hdvd : l ^ 2 ∣ i
  · rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [coeff_zero_eq_constantCoeff_apply, he0, norm_zero] at hi1
      exact absurd hi1 zero_ne_one
    · rw [← le_antisymm hi (Nat.le_of_dvd hpos hdvd)]
      exact hi1
  · have h1 := hc i
    rw [map_sub, coeff_subst_X_pow hq0, if_neg hdvd, sub_zero, hi1] at h1
    exact absurd h1 (not_le.2 hF.norm_l)

end ReciprocityTheory.ChartRestriction.L1
