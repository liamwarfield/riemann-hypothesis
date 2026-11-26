module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.UniqInvHolds
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedFDerivAlgebraicDirectionsJetTransport

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCardWordsLe
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem words_real_bound {x e G F m n : ℝ} {k : ℕ} (hx : 1 < x) (he : 0 < e) (hG : 1 ≤ G) (hF : 1 ≤ F)
    (hm0 : 0 ≤ m) (hn0 : 0 ≤ n) (hm : m ≤ 2 * Real.sqrt (x * x ^ (-(e / 8)))) (hn : n ≤ 2 * x ^ (2 + 8 * e))
    (hk : x ^ (9 / 2 + 10 * e) ≤ (k : ℝ)) (hk3 : 3 ≤ k)
    (hK : 2 * (256 * G + F + 2) + 3 ≤ x ^ e) :
    3 * Real.exp (G * m ^ 5 * (2 * n) * x ^ e) ^ 2 * x ^ F ≤ (2 : ℝ) ^ (k - 3) := by
  have hx0 : 0 < x := by linarith
  set y := x ^ (9 / 2 + 9 * e) with hy
  have hxy : x ≤ y := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ y := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hy1 : 1 ≤ y := by linarith
  have hm' : m ≤ 2 * x ^ (1 / 2 : ℝ) := by
    refine hm.trans ?_
    rw [← Real.sqrt_eq_rpow]
    have h1 : x ^ (-(e / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by linarith)
    have : Real.sqrt (x * x ^ (-(e / 8))) ≤ Real.sqrt x := Real.sqrt_le_sqrt (by nlinarith)
    linarith
  have hm5 : m ^ 5 ≤ 32 * x ^ (5 / 2 : ℝ) := by
    have h1 : m ^ 5 ≤ (2 * x ^ (1 / 2 : ℝ)) ^ 5 := pow_le_pow_left₀ hm0 hm' 5
    have h2 : (x ^ (1 / 2 : ℝ)) ^ 5 = x ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    rw [mul_pow, h2] at h1
    linarith
  have hprod : x ^ (5 / 2 : ℝ) * x ^ (2 + 8 * e) * x ^ e = y := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, hy]; congr 1; ring
  have hxe : 0 < x ^ e := Real.rpow_pos_of_pos hx0 e
  have hA : m ^ 5 * (2 * n) * x ^ e ≤ 128 * y := by
    rw [← hprod]
    have h1 : m ^ 5 * (2 * n) ≤ (32 * x ^ (5 / 2 : ℝ)) * (2 * (2 * x ^ (2 + 8 * e))) :=
      mul_le_mul hm5 (by linarith) (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_right h1 hxe.le
    linarith
  have hky : y * x ^ e ≤ (k : ℝ) := by
    refine le_trans (le_of_eq ?_) hk
    rw [hy, ← Real.rpow_add hx0]; congr 1; ring
  have hlogx : Real.log x ≤ y := by
    have := Real.log_le_sub_one_of_pos hx0
    linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hk' : 2 * ((256 * G + F + 2) * y) ≤ ((k - 3 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk3]
    push_cast
    have := mul_le_mul_of_nonneg_left hK (by linarith : (0 : ℝ) ≤ y)
    nlinarith
  have hR : (2 : ℝ) ^ (k - 3) = Real.exp (((k - 3 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hR, Real.rpow_def_of_pos hx0 F, ← Real.exp_nat_mul]
  calc 3 * Real.exp (((2 : ℕ) : ℝ) * (G * m ^ 5 * (2 * n) * x ^ e)) * Real.exp (Real.log x * F)
      ≤ Real.exp 2 * Real.exp (((2 : ℕ) : ℝ) * (G * m ^ 5 * (2 * n) * x ^ e)) * Real.exp (Real.log x * F) := by
        gcongr
    _ = Real.exp (2 + ((2 : ℕ) : ℝ) * (G * m ^ 5 * (2 * n) * x ^ e) + Real.log x * F) := by
        rw [Real.exp_add, Real.exp_add]
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have h1 : G * (m ^ 5 * (2 * n) * x ^ e) ≤ G * (128 * y) :=
          mul_le_mul_of_nonneg_left hA (by linarith)
        have h2 : Real.log x * F ≤ y * F := mul_le_mul_of_nonneg_right hlogx (by linarith)
        have h4 : ((k - 3 : ℕ) : ℝ) * (1 / 2) ≤ ((k - 3 : ℕ) : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
        push_cast
        nlinarith

theorem szRow_card_words_le : SzRow (fun C D L => (Fintype.card D.what₂.Word ≤ 2 ^ (D.R.k - 3))) := by
  intro eps he he' C hC
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hP, -, hmid, -⟩ := hC
  have hG : 1 ≤ C.CGam := hmid _ (by simp [FC.cMid])
  have hF : 1 ≤ C.P.CF := hmid _ (by simp [FC.cMid])
  have hG' : 1 ≤ C.CGam * C.P.Cpde := by nlinarith
  have hP0 : 0 < C.P.Cpde := by linarith
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨(2 * (256 * (C.CGam * C.P.Cpde) + C.P.CF + 2) + 3) ^ eps⁻¹, ?_⟩⟩⟩
  intro D L hLe hx hV
  have hK : 2 * (256 * (C.CGam * C.P.Cpde) + C.P.CF + 2) + 3 ≤ L.sc.x ^ eps := by
    have h0 : (0 : ℝ) ≤ 2 * (256 * (C.CGam * C.P.Cpde) + C.P.CF + 2) + 3 := by linarith
    have := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hx he.le
    rwa [Real.rpow_inv_rpow h0 he.ne'] at this
  have hn0 := hV.ranks.n_le_of_o hV.host.o_le
  obtain ⟨-, ⟨-, hm⟩, ⟨hk, -⟩, -⟩ := hV.ranks
  have hk3 : 3 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  rw [hV.words, Nat.ceil_le]
  rw [hLe] at hn0 hk
  have hn : (D.R.n : ℝ) / C.P.Cpde ≤ 2 * L.sc.x ^ (2 + 8 * eps) := by
    rw [div_le_iff₀ hP0]; linarith
  simp only [Scale.delta1, hLe] at hm
  have := words_real_bound L.sc.one_lt_alt he hG' hF (Nat.cast_nonneg D.R.m)
    (div_nonneg (Nat.cast_nonneg D.R.n) hP0.le) hm hn hk hk3 hK
  have e : C.CGam * C.P.Cpde * (D.R.m : ℝ) ^ 5 * (2 * ((D.R.n : ℝ) / C.P.Cpde))
      = C.CGam * (D.R.m : ℝ) ^ 5 * (2 * (D.R.n : ℝ)) := by
    field_simp
  rw [e] at this
  simp only [GamL, Scale.L, Ranks.f, hV.CGam_eq, hLe]
  push_cast
  exact this

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSigGaps
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rankVal_crude (s : Scale) (R : Ranks) (hx : 2 ≤ s.x) (h : RankVal s R) :
    (0 < (R.n : ℝ) ∧ (R.n : ℝ) ≤ s.x ^ 4) ∧ (R.m : ℝ) ≤ s.x ^ 2 ∧ (R.k : ℝ) ≤ s.x ^ 6 := by
  have hn1 := h.n_lo
  have hn2 := h.n_le'
  obtain ⟨-, ⟨-, hm⟩, ⟨-, hk⟩, -⟩ := h
  have hx1 : 1 ≤ s.x := by linarith
  have hx0 : 0 < s.x := by linarith
  have he := s.eps_pos
  have he' := s.eps_lt
  refine ⟨⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hn1, ?_⟩, ?_, ?_⟩
  · have h1 : s.x ^ ((9 : ℝ) / 4) ≤ s.x ^ ((3 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; norm_num)
    rw [Real.rpow_natCast] at h1
    have h2 : 0 < s.x ^ 3 := by positivity
    have h3 : s.x ^ 4 = s.x * s.x ^ 3 := by ring
    nlinarith
  · have h1 : s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have h2 : Real.sqrt (s.x * s.delta1) ≤ s.x := by
      apply Real.sqrt_le_iff.2
      refine ⟨hx0.le, ?_⟩
      nlinarith
    nlinarith
  · have h1 : s.x ^ (9 / 2 + 10 * s.eps) ≤ s.x ^ ((5 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
    rw [Real.rpow_natCast] at h1
    have h2 : 0 < s.x ^ 5 := by positivity
    have h3 : s.x ^ 6 = s.x * s.x ^ 5 := by ring
    nlinarith

theorem gap_crude (x C k m t : ℝ) (hx : 2 ≤ x) (hC : C ≤ x) (hk0 : 0 ≤ k) (hm0 : 0 ≤ m) (ht0 : 0 ≤ t)
    (hm : m ≤ x ^ 2) (hk : k ≤ x ^ 6) (ht : t ≤ x ^ 401) :
    C * k * m ^ 4 + (k + m * (t + 1)) * m ^ 10 < x ^ 430 := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have a1 : C * k * m ^ 4 ≤ x * x ^ 6 * (x ^ 2) ^ 4 := by
    have : C * k * m ^ 4 ≤ x * k * m ^ 4 := by gcongr
    refine this.trans ?_
    gcongr
  have a2 : (1 : ℝ) ≤ x ^ 401 := one_le_pow₀ hx1
  have a3 : (k + m * (t + 1)) * m ^ 10 ≤ (x ^ 6 + x ^ 2 * (x ^ 401 + x ^ 401)) * (x ^ 2) ^ 10 := by gcongr
  have a4 : x * x ^ 6 * (x ^ 2) ^ 4 = x ^ 15 := by ring
  have a5 : (x ^ 6 + x ^ 2 * (x ^ 401 + x ^ 401)) * (x ^ 2) ^ 10 = x ^ 26 + 2 * x ^ 423 := by ring
  have a6 : x ^ 15 ≤ x ^ 423 := pow_le_pow_right₀ hx1 (by norm_num)
  have a7 : x ^ 26 ≤ x ^ 423 := pow_le_pow_right₀ hx1 (by norm_num)
  have a8 : (2 : ℝ) ^ 7 ≤ x ^ 7 := by gcongr
  have a9 : x ^ 430 = x ^ 7 * x ^ 423 := by ring
  have a10 : 0 < x ^ 423 := by positivity
  have a11 : 2 ^ 7 * x ^ 423 ≤ x ^ 7 * x ^ 423 := by gcongr
  rw [a9]
  rw [a4] at a1
  rw [a5] at a3
  generalize x ^ 423 = y at *
  linarith

theorem base_sizes_ge (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ (s : Scale) (n : ℕ), s.eps = eps → x0 ≤ s.x →
    0 < (n : ℝ) → (n : ℝ) ≤ s.x ^ 4 → s.x ^ 430 ≤ s.b ∧ s.x ^ 430 ≤ s.b' ∧ s.x ^ 430 ≤ s.w'' n := by
  obtain ⟨x0, h0⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps 434 1 1 0 (by positivity)
    (by linarith) one_pos
  refine ⟨x0, fun s n hs hx hn0 hn => ?_⟩
  have hx1 : 1 ≤ s.x := s.one_lt_alt.le
  have hx0 : 0 < s.x := by linarith
  have h1 := h0 s.x hx
  rw [← hs] at h1
  simp only [pow_zero, one_mul, mul_one] at h1
  have hX0 : 0 < s.X' := Real.exp_pos _
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have h2 : s.x ^ 434 * s.X' ≤ s.b := by
    have e : s.x ^ 434 = Real.exp (434 * Real.log s.x) := by
      rw [show (434 : ℝ) = ((434 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hx0]
    rw [e, Scale.X', Scale.b, Scale.L, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have h3 : s.x ^ 430 ≤ s.x ^ 434 := pow_le_pow_right₀ hx1 (by norm_num)
  have h4 : s.x ^ 434 ≤ s.b / s.X' := (le_div_iff₀ hX0).2 h2
  have h5 : 0 < s.x ^ 434 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · exact h3.trans ((le_mul_of_one_le_right h5.le hX1).trans h2)
  · have e : s.b' = s.x * (s.b / s.X') := by rw [Scale.b', Scale.a]; ring
    rw [e]
    exact h3.trans (h4.trans (le_mul_of_one_le_left (h5.le.trans h4) hx1))
  · have e : s.w'' n = (s.b / s.X') / n := by
      rw [Scale.w'', Scale.b', Scale.a]; field_simp
    rw [e, le_div_iff₀ hn0]
    refine le_trans ?_ h4
    calc s.x ^ 430 * n ≤ s.x ^ 430 * s.x ^ 4 := by gcongr
      _ = s.x ^ 434 := by ring

theorem szRow_sig_gaps : SzRow (fun C D L => (∀ τ, (∀ (i : ℕ) (h : i + 1 < D.R.k - 1), gapS D C.P.Cgap < (((D.hc τ).v ⟨i, by omega⟩ - (D.hc τ).v ⟨i + 1, h⟩ : ℚ) : ℝ)) ∧ (∀ (hk : 2 ≤ D.R.k) (hm : 0 < D.R.m), gapS D C.P.Cgap < (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ + (D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ)) ∧ (∀ (j : ℕ) (h : j + 1 < D.R.m), gapS D C.P.Cgap < (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ)))) := by
  intro eps he _ C hC
  obtain ⟨x0, hx0⟩ := base_sizes_ge eps he
  refine ⟨430, fun cD hcD => ⟨430, fun ch hch => ⟨max x0 (max 2 C.P.Cgap), fun D L hs hx hV => ?_⟩⟩⟩
  have hxa : x0 ≤ L.sc.x := (le_max_left _ _).trans hx
  have hx2 : 2 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxC : C.P.Cgap ≤ L.sc.x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx1 : 1 ≤ L.sc.x := by linarith
  obtain ⟨⟨hn0, hn⟩, hm, hk⟩ := rankVal_crude L.sc D.R hx2 hV.ranks
  obtain ⟨hb, hb', hw⟩ := hx0 L.sc D.R.n hs hxa hn0 hn
  have ht : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by
    have h1 := L.t_win.2
    rw [hV.Ct_eq, hC.1.2.2.2.2.2.2.2.2.2, show (401 : ℝ) = ((401 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
    exact h1
  have hg : gapS D C.P.Cgap < L.sc.x ^ 430 := by
    have := gap_crude L.sc.x C.P.Cgap D.R.k D.R.m D.R.t hx2 hxC (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) hm hk ht
    unfold gapS Ranks.N
    push_cast
    exact this
  have hp : 0 < L.sc.x ^ 430 := by positivity
  have hpow : ∀ c : ℝ, 430 ≤ c → L.sc.x ^ 430 ≤ (⌈L.sc.x ^ c⌉₊ : ℝ) := by
    intro c hc
    refine le_trans ?_ (Nat.le_ceil _)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; exact hc)
  obtain ⟨hv, -, ⟨b1, hbj, htop, hthick, hthin⟩, -⟩ := hV.hc
  have hb1 : ∀ τ, L.sc.x ^ 430 ≤ (b1 τ : ℝ) := by
    intro τ
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      unfold Host.topPlaces at h1
      obtain ⟨t, htT, hteq⟩ := Finset.mem_image.1 h1
      rw [htop τ ⟨t, htT⟩ hteq.symm]
      have h2 := L.bT_ge ⟨t, htT⟩
      have h3 : (0 : ℝ) ≤ (⌊L.sc.b' / L.sc.x⌋ : ℤ) := by
        exact_mod_cast Int.floor_nonneg.2 (div_nonneg (by linarith) (by linarith))
      push_cast
      linarith
    · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · have h3 := Int.le_ceil L.sc.b
        have h4 : ((⌈L.sc.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast (hthick τ h2).1
        linarith
      · rw [hthin τ ⟨(D.eTau τ).2, h1, h2⟩]
        exact hw.trans (Int.le_ceil _)
  generalize L.sc.x ^ 430 = y at *
  intro τ
  refine ⟨fun i h => ?_, fun hk2 hm0 => ?_, fun j h => ?_⟩
  · rw [hv, hv]
    have e : D.R.k - 2 - i = (D.R.k - 2 - (i + 1)) + 1 := by omega
    simp only [e]
    have := hpow cD hcD
    unfold Delv
    push_cast
    linarith
  · rw [hv, (hbj τ _).1]
    have := hb1 τ
    simp only [Nat.sub_self]
    push_cast
    linarith
  · rw [(hbj τ _).1, (hbj τ _).1]
    have := hpow ch hch
    unfold h0v
    push_cast
    linarith

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UniformizationHolds
noncomputable section

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

abbrev cj : ℂ →+ ℂ := (starRingEnd ℂ).toAddMonoidHom

theorem cj_apply (z : ℂ) : cj z = starRingEnd ℂ z := rfl

theorem map_cj_map_cj (Λ : AddSubgroup ℂ) : (Λ.map cj).map cj = Λ := by
  rw [AddSubgroup.map_map]
  have : cj.comp cj = AddMonoidHom.id ℂ := by ext z; simp [cj_apply]
  rw [this, AddSubgroup.map_id]

theorem eisG_map_cj (Λ : AddSubgroup ℂ) (k : ℕ) :
    eisG (Λ.map cj) k = starRingEnd ℂ (eisG Λ k) := by
  unfold eisG
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ Λ.map cj ∧ w ≠ 0} :=
    { toFun := fun w => ⟨starRingEnd ℂ w.1, ⟨w.1, w.2.1, rfl⟩, by simpa using w.2.2⟩
      invFun := fun w => ⟨starRingEnd ℂ w.1, by
          obtain ⟨v, hv, hv'⟩ := AddSubgroup.mem_map.1 w.2.1
          have : starRingEnd ℂ w.1 = v := by rw [← hv']; simp [cj_apply]
          rw [this]; exact hv, by simpa using w.2.2⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  rw [← e.tsum_eq, Complex.conj_tsum]
  congr 1
  ext w
  show (1 : ℂ) / (starRingEnd ℂ (w : ℂ)) ^ (2 * k) = starRingEnd ℂ (1 / (w : ℂ) ^ (2 * k))
  simp [map_div₀, map_pow]

theorem eisenstein_g_two_map_conj (Λ : AddSubgroup ℂ) : g2 (Λ.map cj) = starRingEnd ℂ (g2 Λ) := by
  unfold g2; rw [eisG_map_cj, map_mul, map_ofNat]

theorem eisenstein_g_three_map_conj (Λ : AddSubgroup ℂ) : g3 (Λ.map cj) = starRingEnd ℂ (g3 Λ) := by
  unfold g3; rw [eisG_map_cj, map_mul, map_ofNat]

theorem discr_map_cj (Λ : AddSubgroup ℂ) :
    Formalism.MainNotions.TaylorLogMetric.discr (Λ.map cj) = starRingEnd ℂ (Formalism.MainNotions.TaylorLogMetric.discr Λ) := by
  unfold Formalism.MainNotions.TaylorLogMetric.discr; rw [eisenstein_g_two_map_conj, eisenstein_g_three_map_conj, map_sub, map_mul, map_pow, map_pow, map_ofNat]

theorem lamConj_spec (hU : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization) (M : IntermediateField ℚ ℂ)
    (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M) (h1 : Formalism.MainNotions.TaylorLogMetric.discr Λ = 1) :
    g2 (lamConj M ρ Λ) = ρ ⟨g2 Λ, h2⟩ ∧ g3 (lamConj M ρ Λ) = ρ ⟨g3 Λ, h3⟩ ∧
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ Λ) = 1 := by
  have hl2 : liftM M (g2 Λ) = ⟨g2 Λ, h2⟩ := dif_pos h2
  have hl3 : liftM M (g3 Λ) = ⟨g3 Λ, h3⟩ := dif_pos h3
  have hdM : (⟨g2 Λ, h2⟩ : M) ^ 3 - 27 * (⟨g3 Λ, h3⟩ : M) ^ 2 = 1 := by
    apply M.val.injective
    rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one]
    exact h1
  have hab : (ρ ⟨g2 Λ, h2⟩) ^ 3 - 27 * (ρ ⟨g3 Λ, h3⟩) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hdM, map_one]
  obtain ⟨Λ', -, h2', h3'⟩ := (hU _ _ (by rw [hab]; exact one_ne_zero)).1
  have hex : ∃ Λ' : AddSubgroup ℂ, g2 Λ' = ρ (liftM M (g2 Λ)) ∧ g3 Λ' = ρ (liftM M (g3 Λ)) :=
    ⟨Λ', by rw [hl2]; exact h2', by rw [hl3]; exact h3'⟩
  have hs := Classical.epsilon_spec hex
  have e2 : g2 (lamConj M ρ Λ) = ρ ⟨g2 Λ, h2⟩ := hs.1.trans (by rw [hl2])
  have e3 : g3 (lamConj M ρ Λ) = ρ ⟨g3 Λ, h3⟩ := hs.2.trans (by rw [hl3])
  refine ⟨e2, e3, ?_⟩
  show g2 _ ^ 3 - 27 * g3 _ ^ 2 = 1
  rw [e2, e3, hab]

def conjO (D : D7) : 𝓞 D.host.K ≃+* 𝓞 D.host.K :=
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  RingOfIntegers.mapRingEquiv
    ((AlgEquiv.restrictNormal D.host.conj D.host.K : D.host.K ≃ₐ[ℚ] D.host.K) : D.host.K ≃+* D.host.K)

theorem phi_conjO (D : D7) (a : 𝓞 D.host.K) :
    D.host.φ₀ (((conjO D a : 𝓞 D.host.K) : D.host.K) : D.host.E) =
      starRingEnd ℂ (D.host.φ₀ ((a : D.host.K) : D.host.E)) := by
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  have h : (((conjO D a : 𝓞 D.host.K) : D.host.K) : D.host.E) = D.host.conj ((a : D.host.K) : D.host.E) := by
    rw [conjO, RingOfIntegers.mapRingEquiv_apply]
    exact AlgEquiv.restrictNormal_commutes D.host.conj D.host.K (a : D.host.K)
  rw [h]
  exact D.host.toHostAx.conjE_apply _ _

theorem lamOf_map_cj (D : D7) (c : Ideal (𝓞 D.host.K)) (x : ℂ) :
    (lamOf D c x).map cj = lamOf D (c.map (conjO D)) (starRingEnd ℂ x) := by
  unfold lamOf
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨conjO D a, Ideal.mem_map_of_mem _ ha, ?_⟩
    rw [phi_conjO, cj_apply, map_mul]
  · rintro ⟨b, hb, rfl⟩
    rw [Ideal.mem_map_of_equiv] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨_, ⟨a, ha, rfl⟩, by rw [phi_conjO, cj_apply, map_mul]⟩

end GlobalTheory.ConjLattice

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem containsData {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {M : IntermediateField ℚ ℂ}
    (h : DataIn D (tor0 D cc δ) M) : EquidistributedConjugates.ContainsData D M (lamOf D cc δ) := by
  refine ⟨fun x => ?_, h.2.1, h.2.2⟩
  have := h.1 (D.eTau.symm 1) (x : D.host.E)
  rwa [show (tor0 D cc δ).emb (D.eTau.symm 1) (x : D.host.E) = embT D (D.eTau.symm 1) (x : D.host.E) from rfl,
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D _ _ x.2] at this

theorem conj_lattice : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization →
    EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta →
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x := by
  intro hU hCE _ D cc δ M _ t hS ρ
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have h1 : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have h2 : g2 (lamOf D cc δ) ∈ M := hM.2.1
  have h3 : g3 (lamOf D cc δ) ∈ M := hM.2.2
  have hsp := fun ρ' => lamConj_spec hU M ρ' (lamOf D cc δ) h2 h3 h1
  refine ⟨(hsp ρ).2.2, ?_⟩
  obtain ⟨⟨c, hcH, -⟩, hC2, -⟩ := hCE D cc δ hcc hδ M (containsData hM)
  by_cases hρ : EquidistributedConjugates.FixesK D M ρ
  · obtain ⟨x, hx, hxe⟩ := hcH ⟨ρ, hρ⟩
    exact ⟨_, nonZeroDivisors.coe_ne_zero _, x, hx, hxe⟩
  · obtain ⟨hρ', -⟩ := hC2 ρ hρ
    obtain ⟨x, hx, hxe⟩ := hcH ⟨EquidistributedConjugates.conjEmb M ρ, hρ'⟩
    have hUI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.UniqInv :=
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqInv_of_lat Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds hU
    have hmap : (lamConj M ρ (lamOf D cc δ)).map cj = lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ) := by
      apply hUI
      · rw [discr_map_cj, (hsp ρ).2.2, map_one]; exact one_ne_zero
      · rw [eisenstein_g_two_map_conj, (hsp ρ).1, (hsp _).1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
      · rw [eisenstein_g_three_map_conj, (hsp ρ).2.1, (hsp _).2.1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
    have hback : lamConj M ρ (lamOf D cc δ) = (lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ)).map cj := by
      rw [← hmap, map_cj_map_cj]
    refine ⟨(c ⟨EquidistributedConjugates.conjEmb M ρ, hρ'⟩ : Ideal (𝓞 D.host.K)).map (conjO D), ?_, starRingEnd ℂ x,
      (map_ne_zero _).2 hx, by rw [hback, hxe, lamOf_map_cj]⟩
    intro hbot
    rw [Ideal.map_eq_bot_iff_of_injective (conjO D).injective] at hbot
    exact nonZeroDivisors.coe_ne_zero _ hbot

end GlobalTheory.ConjLattice

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem uniformization_holds : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization := by
  intro a b h
  refine ⟨?_, fun Λ Λ' hΛ hΛ' h2 h3 h2' h3' =>
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqLat_holds Λ Λ' hΛ hΛ' (h2.trans h2'.symm) (h3.trans h3'.symm)⟩
  obtain ⟨L, h2, h3⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants h
  obtain ⟨e2, e3, hΔ, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L L.lattice.toAddSubgroup (fun _ => Iff.rfl)
  exact ⟨_, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds _ hΔ, e2.trans h2, e3.trans h3⟩

theorem conj_lattice_holds : EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta →
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x :=
  conj_lattice uniformization_holds

end GlobalTheory.ConjLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicJetsOfAlgebraicTaylor
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicJetsOfAlgebraicTaylor
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.AlgJetsRat

variable {D : D7} {N N' : ℕ}

theorem jet_embV_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (F : VC D N N' → ℂ) (hF : ContDiff ℂ ⊤ F)
    (hT : ∀ α, taylor D F α ∈ Qbar) {m : ℕ} (A : Fin m → Matrix (Fin N') (Fin N) D.host.E) :
    iteratedFDeriv ℂ m F 0 (fun j => embV D (tor0 D cc δ) (A j)) ∈ Qbar := by
  rw [GlobalTheory.JetTransport.mlin_expand]
  refine IntermediateField.sum_mem _ fun f _ => IntermediateField.mul_mem _ ?_ ?_
  · exact IntermediateField.prod_mem _ fun j _ => GlobalTheory.JetTransport.embT_mem _ _
  · rw [GlobalTheory.JetTransport.iFD_coord F hF f]
    refine IntermediateField.mul_mem _ (IntermediateField.prod_mem _ fun i _ => ?_) (hT _)
    exact IntermediateField.natCast_mem _ _

end GlobalTheory.AlgJetsRat

open GlobalTheory.AlgJetsRat in
theorem GlobalTheory.algJets_of_taylor : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (F : VC D N N' → ℂ), δ / δ₀ ∈ Qbar → δ₀ ≠ 0 → ContDiff ℂ ⊤ F → (∀ α, taylor D F α ∈ Qbar) → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x ∈ La D B.tor L L', ∃ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), 0 < n ∧ x = δ • embV D B.tor A ∧ (n : D.host.E) • A ∈ YYl D L L') → S.AlgJets δ₀ (fun z => F (e.symm z)) := by
  intro D cc δ δ₀ B N N' L L' F hδ hδ₀ hF hT g S e he hLa k ys hys
  have hc : ∀ j, ∃ (c : ℂ) (A : Matrix (Fin N') (Fin N) D.host.E),
      c ∈ Qbar ∧ e.symm (δ₀⁻¹ • ys j) = c • embV D B.tor A := by
    intro j
    obtain ⟨s, hs, hsy⟩ := hys j
    have hx : e.symm ((s : ℂ) • ys j) ∈ La D B.tor L L' := (he _).1 (by simpa using hsy)
    obtain ⟨n, A, -, hA, -⟩ := hLa _ hx
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    refine ⟨δ / δ₀ * (s : ℂ)⁻¹, A, IntermediateField.mul_mem _ hδ
      (IntermediateField.inv_mem _ (IntermediateField.natCast_mem _ s)), ?_⟩
    have h1 : e.symm (ys j) = (s : ℂ)⁻¹ • (δ • embV D B.tor A) := by
      rw [← hA, map_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [map_smul, h1, smul_smul, smul_smul]
    congr 1
    field_simp
  choose c A hcQ hcA using hc
  show iteratedFDeriv ℂ k (F ∘ ((e.symm : (Fin g → ℂ) ≃L[ℂ] VC D N N') : (Fin g → ℂ) →L[ℂ] VC D N N')) 0
    (fun j => δ₀⁻¹ • ys j) ∈ Qbar
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hF _ le_top,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [ContinuousLinearEquiv.coe_coe, map_zero, hcA]
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  exact IntermediateField.mul_mem _ (IntermediateField.prod_mem _ fun j _ => hcQ j)
    (jet_embV_mem cc δ F hF hT A)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicJetsOfAlgebraicTaylorStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicJets_of_algebraic_taylor : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (F : VC D N N' → ℂ), δ / δ₀ ∈ Qbar → δ₀ ≠ 0 → ContDiff ℂ ⊤ F → (∀ α, taylor D F α ∈ Qbar) → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x ∈ La D B.tor L L', ∃ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), 0 < n ∧ x = δ • embV D B.tor A ∧ (n : D.host.E) • A ∈ YYl D L L') → S.AlgJets δ₀ (fun z => F (e.symm z)) := by
  first | exact @GlobalTheory.algJets_of_taylor | exact GlobalTheory.algJets_of_taylor | (intros; apply GlobalTheory.algJets_of_taylor <;> assumption)
end
end
