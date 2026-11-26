module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AutomorphicArithmetic.CyclotomicBounds.PlaceOfLetterInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleLogMulLeSizeRatio

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizesSumLePageHeight
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem bHat_add_etaHat_add_sHat_le_hPage {D : D7} (L : SizeData₂ D) (C : ℝ) (h : Roomy L C) :
    (bHat L : ℝ) + (etaHat L : ℝ) + (sHat L : ℝ) ≤ hPage L := by
  have ht : 5 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hη : 0 < L.etaSz := L.etaSz_pos
  have hS : 0 < L.Sc := L.Sc_pos
  obtain ⟨hC, hw1, hw2, hwb, -, hb⟩ := h
  have hLw : (0 : ℝ) ≤ (D.host.Lw : ℝ) := Nat.cast_nonneg _
  have hb' : (100 : ℝ) ≤ L.sc.b' := hw1.trans hwb
  have hfac : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbig : 100 * L.sc.b' ≤ L.sc.b := by
    have := mul_le_mul_of_nonneg_right hfac (by linarith : (0 : ℝ) ≤ L.sc.b')
    linarith
  have htR : ((D.R.t : ℕ) : ℝ) ≤ L.sc.b := by nlinarith
  have hb0 : 0 ≤ L.sc.b := by linarith
  set c := (D.R.t + 1) / 2 with hcdef
  have hc3 : 3 ≤ c := by omega
  have hct : c ≤ D.R.t := by omega
  have htc : D.R.t ≤ ⌈L.sc.b⌉₊ := by exact_mod_cast htR.trans (Nat.le_ceil _)
  have hcle : c ≤ ⌈L.sc.b⌉₊ := hct.trans htc
  have h1 : (⌈L.sc.b⌉₊ : ℝ) < L.sc.b + 1 := Nat.ceil_lt_add_one hb0
  have h2 : (⌊L.etaSz⌋₊ : ℝ) ≤ L.etaSz := Nat.floor_le hη.le
  have h3 : (⌊L.Sc⌋₊ : ℝ) ≤ L.Sc := Nat.floor_le hS.le
  have hc3R : (3 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc3
  unfold bHat etaHat sHat hPage
  rw [← hcdef, Nat.cast_sub hcle]
  push_cast
  linarith

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowAndBlockExponentOfEmbeddings
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowAndBlockExponentOfEmbeddings
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem window_and_cTB_of_jumps_at_embeddings :
    ∀ (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (h r n t : ℕ) [CharZero S.Qp] [FiniteDimensional S.Qp S.K], S.W.s = 1 → Nat.card (S.K →ₐ[S.Qp] S.LL) = finrank S.Qp S.K → finrank S.Qp S.K ≤ n → LocalSituation.gK S = 0 → LocalSituation.vdegMs S (LocalSituation.mN (LocalSituation.ell S) 1 (h + h)) = LocalSituation.mN (LocalSituation.ell S) 1 (h + h) - 1 → t ≤ h → (∀ τ : S.K →ₐ[S.Qp] S.LL, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u + 1 ≤ h) ∧ ∀ a, IsJumpV S.PD Y.ρ τ a → a ∈ U) → (∀ a ∈ LocalSituation.Jset S Y, -(h : ℤ) ≤ a ∧ a ≤ h) ∧ ∀ e < t, LocalSituation.cTBY S Y h h e ≤ cBnum (LocalSituation.ell S) h t (n * r) := by
  intro S Y h r n t _ _ hs hcard hn hg hv hth hU
  classical
  choose U hUc hUb hUj using hU
  have hpos : 0 < finrank S.Qp S.K := finrank_pos
  have hfin : Finite (S.K →ₐ[S.Qp] S.LL) := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype (S.K →ₐ[S.Qp] S.LL) := Fintype.ofFinite _
  have hsub : LocalSituation.Jset S Y ⊆ ((Finset.univ.biUnion U : Finset ℤ) : Set ℤ) := by
    intro a ha
    obtain ⟨τ, hτ⟩ := jump_of_total S.PD Y.ρ hcard a ha
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ _, hUj τ a hτ⟩)
  have hb : ∀ u ∈ Finset.univ.biUnion U, -(h : ℤ) ≤ u ∧ u + 1 ≤ h := by
    intro u hu
    obtain ⟨τ, -, hτ⟩ := Finset.mem_biUnion.1 hu
    exact hUb τ u hτ
  have hc : (Finset.univ.biUnion U).card ≤ n * r := by
    refine (Finset.card_biUnion_le_card_mul _ _ r fun τ _ => hUc τ).trans (Nat.mul_le_mul_right _ ?_)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
    exact hn
  refine ⟨fun a ha => ?_, fun e he => ?_⟩
  · have := hb a (Finset.mem_coe.1 (hsub ha))
    omega
  · unfold LocalSituation.cTBY
    rw [hg, hs, hv]
    exact cTB_le (LocalSituation.ell S) h t (n * r) e S.PD.hp _ _ hsub hc hb he hth

end GlobalTheory.HubLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowAndBlockExponentOfEmbeddingsStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jumpWindow_and_blockExponent_of_embeddings : ∀ (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (h r n t : ℕ) [CharZero S.Qp] [FiniteDimensional S.Qp S.K], S.W.s = 1 → Nat.card (S.K →ₐ[S.Qp] S.LL) = finrank S.Qp S.K → finrank S.Qp S.K ≤ n → LocalSituation.gK S = 0 → LocalSituation.vdegMs S (LocalSituation.mN (LocalSituation.ell S) 1 (h + h)) = LocalSituation.mN (LocalSituation.ell S) 1 (h + h) - 1 → t ≤ h → (∀ τ : S.K →ₐ[S.Qp] S.LL, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u + 1 ≤ h) ∧ ∀ a, IsJumpV S.PD Y.ρ τ a → a ∈ U) → (∀ a ∈ LocalSituation.Jset S Y, -(h : ℤ) ≤ a ∧ a ≤ h) ∧ ∀ e < t, LocalSituation.cTBY S Y h h e ≤ cBnum (LocalSituation.ell S) h t (n * r) := by
  first | exact @GlobalTheory.HubLoc.window_and_cTB_of_jumps_at_embeddings | exact GlobalTheory.HubLoc.window_and_cTB_of_jumps_at_embeddings | (intros; apply GlobalTheory.HubLoc.window_and_cTB_of_jumps_at_embeddings <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtMostTwoThickInWindowLongOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtMostTwoThickInWindowLongOrbit
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.LongWindow

theorem thick_inTranslate {R : Ranks} (H : Host R) (g : R.GG) (hg : Thick H g) :
    R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv g.2) := by
  unfold Thick Host.thickPlaces at hg
  obtain ⟨s, hs, e⟩ : ∃ s ∈ H.T2, R.tau2 (R.dig s + H.u0) = plc g := by
    simpa [Finset.mem_image] using hg
  refine ⟨s, hs, ?_⟩
  have e2 : (plc g).2 = g.2 := UpperTheory.KStar.Words.placeOf_snd g
  rw [← e2, ← e]
  rfl

theorem letter_snd {fr : Formalism.HC.Frame} (τ φ : fr.GG) (i : ZMod (orderOf φ)) (k : ℕ) :
    fr.iotaInv (letter τ φ (i + k)).2 = fr.iotaInv τ.2 + (((i.val + k : ℕ) : ℤ)) • fr.iotaInv φ.2 := by
  unfold letter
  rw [UpperTheory.KStar.Words.pow_val_add, natCast_zsmul]
  rfl

open Classical in
theorem main : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 4 * H.Lw < orderOf φ.2 →
    WindowTwo (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) H.Lw := by
  intro R H τ φ hord i a b c hab hbc hcL ⟨ha, hb, hc⟩
  have hO := ((R.toFrame.hostThickOrbit H.T2 H.second_set_range H.second_set_no_relation H.u0 (R.iotaInv τ.2) (R.iotaInv φ.2)).1
    (by rw [R.toFrame.addOrderOf_iotaInv]; exact hord) (i.val : ℤ))
  have mem : ∀ k : ℕ, k < H.Lw → Thick H (letter τ φ (i + k)) →
      ((i.val + k : ℕ) : ℤ) ∈ (Finset.Ico (i.val : ℤ) (i.val + H.Lw)).filter
        (fun j : ℤ => R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv τ.2 + j • R.iotaInv φ.2)) := by
    intro k hk ht
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by push_cast; omega, by push_cast; omega⟩, ?_⟩
    rw [← letter_snd]
    exact thick_inTranslate H _ ht
  have hsub : ({((i.val + a : ℕ) : ℤ), ((i.val + b : ℕ) : ℤ), ((i.val + c : ℕ) : ℤ)} : Finset ℤ) ⊆
      (Finset.Ico (i.val : ℤ) (i.val + H.Lw)).filter
        (fun j : ℤ => R.toFrame.InTranslate H.T2 H.u0 (R.iotaInv τ.2 + j • R.iotaInv φ.2)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem a (by omega) ha
    · exact mem b (by omega) hb
    · exact mem c hcL hc
  have h3 : ({((i.val + a : ℕ) : ℤ), ((i.val + b : ℕ) : ℤ), ((i.val + c : ℕ) : ℤ)} : Finset ℤ).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · push_cast; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; push_cast; omega
  have := Finset.card_le_card hsub
  omega

end GlobalTheory.HTW.LongWindow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtMostTwoThickInWindowLongOrbitStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atMostTwoThick_in_window_long_orbit : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 4 * H.Lw < orderOf φ.2 → WindowTwo (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) H.Lw := by
  first | exact @GlobalTheory.HTW.LongWindow.main | exact GlobalTheory.HTW.LongWindow.main | (intros; apply GlobalTheory.HTW.LongWindow.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PageLargeScaleBoundsOfLargeScale
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThinSizeDominatesAtLargeScale
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThinSizeDominatesAtLargeScale
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem thinSize_dominates : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x0 ≤ L.sc.x → (100 : ℝ) ≤ L.sc.w'' D.R.n ∧ 100 * (L.etaSz + L.Sc + D.R.t + 2) ≤ L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' := by
  intro eps _
  refine ⟨10000, fun D L P _ hx => ?_⟩
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (7 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t; have := D.R.two_le_m; exact_mod_cast (by omega : 7 ≤ D.R.t)
  have hn1 : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.ord_pos
  have hx0 : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hX : 0 < L.sc.X' := Real.exp_pos _
  have hb' : 0 < L.sc.b' := by unfold Scale.b' Scale.a; positivity
  have hxn : 1 ≤ L.sc.x * D.R.n := by nlinarith
  have hw1 : L.sc.w'' D.R.n ≤ L.sc.b' := div_le_self hb'.le hxn
  have hte := P.t_le_eta
  have h1 := P.teta
  rw [le_div_iff₀ hx0] at h1
  have hS := L.Sc_pos
  have hsq : (100 : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have hlog : (1 : ℝ) ≤ Real.log L.sc.x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hk : (200 : ℝ) ≤ D.R.k := by
    refine le_trans ?_ P.k_ge_mx
    have a : (200 : ℝ) ≤ (D.R.m : ℝ) * L.sc.x ^ ((1 : ℝ) / 2) := by nlinarith
    nlinarith
  have h2 : 200 * L.Sc ≤ L.sc.w'' D.R.n :=
    le_trans (mul_le_mul_of_nonneg_right hk hS.le) P.kS_le
  have h3 : 7 * L.etaSz ≤ (D.R.t : ℝ) * L.etaSz := mul_le_mul_of_nonneg_right ht (by linarith)
  have h4 : 7 * L.etaSz * 10000 ≤ L.sc.w'' D.R.n :=
    le_trans (mul_le_mul h3 hx (by norm_num) (by linarith)) h1
  exact ⟨by linarith, by linarith, hw1⟩

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThinSizeDominatesAtLargeScaleStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thinSize_dominates_at_large_scale : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x0 ≤ L.sc.x → (100 : ℝ) ≤ L.sc.w'' D.R.n ∧ 100 * (L.etaSz + L.Sc + D.R.t + 2) ≤ L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' := by
  first | exact @GlobalTheory.HTW.thinSize_dominates | exact GlobalTheory.HTW.thinSize_dominates | (intros; apply GlobalTheory.HTW.thinSize_dominates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopSizeAddLeThreeHalvesScale
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopSizeAddLeThreeHalvesScale
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.Ggeo

theorem bT_add_div_le_three_halves : ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), 4 ≤ L.sc.x →
    ∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b' := by
  intro D L P hx t
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hb' : 0 < L.sc.b' := by
    unfold Formalism.BasicNotions.Scale.b' Formalism.BasicNotions.Scale.a Formalism.BasicNotions.Scale.b Formalism.BasicNotions.Scale.X'
    positivity
  have hbT := P.bT_le t
  have hrho := P.rho_le
  unfold Formalism.BasicNotions.LevelStarExponents.rhoP at hrho
  have hLaG : 0 < L.LaG := by
    have h1 := P.S_le
    have h2 := L.Sc_pos
    by_contra hneg
    have hneg' : L.LaG ≤ 0 := le_of_not_gt hneg
    have h3 : L.LaG * L.sc.b' / (D.R.k : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg' hb'.le) (Nat.cast_nonneg _)
    linarith
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / (D.R.k : ℝ) := by
    have := P.Crho_pos
    positivity
  set T := Formalism.BasicNotions.LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) with hT
  have hT4 : 4 * T ≤ L.sc.x ^ (-2 : ℝ) := by
    have h4 : 4 * Formalism.BasicNotions.LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) = 4 * T := by
      rw [hT]
      ring
    linarith
  have hbT' : (L.bT t : ℝ) ≤ L.sc.b' + T * L.sc.b' := by
    have h5 : Formalism.BasicNotions.LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) = T * L.sc.b' := by
      rw [hT]
      ring
    linarith
  have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 / 16 := by
    calc L.sc.x ^ (-2 : ℝ) = (L.sc.x ^ 2)⁻¹ := by rw [Real.rpow_neg hx0.le, Real.rpow_two]
      _ ≤ (16 : ℝ)⁻¹ := (inv_le_inv₀ (by positivity) (by norm_num)).mpr (by nlinarith)
      _ = 1 / 16 := by norm_num
  have hTb : T * L.sc.b' ≤ L.sc.b' / 64 := by
    have h6 : T ≤ 1 / 64 := by linarith
    nlinarith
  have hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
  linarith

end GlobalTheory.Ggeo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopSizeAddLeThreeHalvesScaleStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topSize_add_le_three_halves_scale : ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), 4 ≤ L.sc.x → ∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b' := by
  first | exact @GlobalTheory.Ggeo.bT_add_div_le_three_halves | exact GlobalTheory.Ggeo.bT_add_div_le_three_halves | (intros; apply GlobalTheory.Ggeo.bT_add_div_le_three_halves <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleLogMulLeSizeRatioStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scale_log_mul_le_size_ratio : ∀ eps C A : ℝ, 0 < eps → 0 ≤ C → 0 ≤ A → ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → C * (A * Real.log s.x + 1) * s.b' ≤ s.b := by
  first | exact @GlobalTheory.scale_log_mul_b'_le_b | exact GlobalTheory.scale_log_mul_b'_le_b | (intros; apply GlobalTheory.scale_log_mul_b'_le_b <;> assumption)
end

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem roomy_of_large : ∀ eps C A : ℝ, 0 < eps → 100 ≤ C → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → Roomy L C := by
  intro eps C A he hC
  have hC0 : (0 : ℝ) ≤ C := by linarith
  obtain ⟨x1, h1⟩ := GlobalTheory.T.thinSize_dominates_at_large_scale eps he
  obtain ⟨x2, h2⟩ := GlobalTheory.T.scale_log_mul_le_size_ratio eps C (max A 0) he hC0 (le_max_right _ _)
  refine ⟨max (max x1 x2) 4, fun D L P hL hA hx => ?_⟩
  have hx1 : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx4 : (4 : ℝ) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  obtain ⟨a1, a2, a3⟩ := h1 D L P hL hx1
  refine ⟨hC, a1, a2, a3, GlobalTheory.T.topSize_add_le_three_halves_scale D L P hx4, ?_⟩
  have hb : (0 : ℝ) ≤ L.sc.b' := by linarith
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg (by linarith)
  have hw : (D.host.Lw : ℝ) ≤ max A 0 * Real.log L.sc.x :=
    P.Lw_le.trans (mul_le_mul_of_nonneg_right (hA.trans (le_max_left _ _)) hlog)
  refine le_trans ?_ (h2 L.sc hL hx2)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC0) hb

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankAddOfBiprod
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits
open Module TensorProduct

noncomputable section

namespace GlobalTheory.HTW.SumJumps

theorem finrank_add_of_biprod {L M M₁ M₂ : Type} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup M₁] [Module L M₁] [AddCommGroup M₂] [Module L M₂]
    (p₁ : M →ₗ[L] M₁) (p₂ : M →ₗ[L] M₂) (i₁ : M₁ →ₗ[L] M) (i₂ : M₂ →ₗ[L] M)
    (h11 : ∀ x, p₁ (i₁ x) = x) (h22 : ∀ x, p₂ (i₂ x) = x) (h12 : ∀ x, p₁ (i₂ x) = 0)
    (h21 : ∀ x, p₂ (i₁ x) = 0) (h : ∀ x, i₁ (p₁ x) + i₂ (p₂ x) = x)
    (S : Submodule L M) (S₁ : Submodule L M₁) (S₂ : Submodule L M₂)
    [Module.Finite L S₁] [Module.Finite L S₂]
    (a₁ : ∀ x ∈ S, p₁ x ∈ S₁) (a₂ : ∀ x ∈ S, p₂ x ∈ S₂) (b₁ : ∀ x ∈ S₁, i₁ x ∈ S)
    (b₂ : ∀ x ∈ S₂, i₂ x ∈ S) : finrank L S = finrank L S₁ + finrank L S₂ := by
  rw [← Module.finrank_prod]
  refine LinearEquiv.finrank_eq (LinearEquiv.ofBijective
    ((p₁.restrict a₁).prod (p₂.restrict a₂)) ⟨?_, ?_⟩)
  · intro x y hxy
    have e1 : p₁ x = p₁ y := congrArg (fun z : S₁ × S₂ => (z.1 : M₁)) hxy
    have e2 : p₂ x = p₂ y := congrArg (fun z : S₁ × S₂ => (z.2 : M₂)) hxy
    apply Subtype.ext
    rw [← h x, ← h y, e1, e2]
  · rintro ⟨x, y⟩
    refine ⟨⟨i₁ x + i₂ y, S.add_mem (b₁ _ x.2) (b₂ _ y.2)⟩, ?_⟩
    ext
    · simp [h11, h12]
    · simp [h21, h22]

section Funct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']

def ext1 (Qp : Type) [Field Qp] {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (C : Type) [AddCommGroup C] [Module Qp C] (f : V →ₗ[LL] V') :
    V ⊗[Qp] C →ₗ[LL] V' ⊗[Qp] C :=
  AlgebraTensorModule.map f LinearMap.id

theorem ext1_comm {C C' : Type} [AddCommGroup C] [Module Qp C] [AddCommGroup C'] [Module Qp C']
    (f : V →ₗ[LL] V') (r : V →ₗ[LL] V) (r' : V' →ₗ[LL] V') (hf : ∀ v, f (r v) = r' (f v))
    (u : C →ₗ[Qp] C') (x : V ⊗[Qp] C) :
    AlgebraTensorModule.map r' u (ext1 Qp C f x) = ext1 Qp C' f (AlgebraTensorModule.map r u x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ext1, hf]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem ext1_comp_ext1 {C : Type} [AddCommGroup C] [Module Qp C]
    (f : V →ₗ[LL] V') (f' : V' →ₗ[LL] V'') (x : V ⊗[Qp] C) :
    ext1 Qp C f' (ext1 Qp C f x) = ext1 Qp C (f' ∘ₗ f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ext1]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem ext1_id {C : Type} [AddCommGroup C] [Module Qp C] (x : V ⊗[Qp] C) :
    ext1 Qp C (LinearMap.id : V →ₗ[LL] V) x = x := by
  simp [ext1]

theorem ext1_zero {C : Type} [AddCommGroup C] [Module Qp C] (x : V ⊗[Qp] C) :
    ext1 Qp C (0 : V →ₗ[LL] V') x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [ext1]
  | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]

theorem ext1_add {C : Type} [AddCommGroup C] [Module Qp C] (f f' : V →ₗ[LL] V') (x : V ⊗[Qp] C) :
    ext1 Qp C f x + ext1 Qp C f' x = ext1 Qp C (f + f') x := by
  simp [ext1, AlgebraTensorModule.map_add_left]

variable {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem dcris_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ Dcris PD ρ, ext1 Qp B f x ∈ Dcris PD ρ' := by
  intro x hx
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  have := hx g
  unfold actVB at this ⊢
  rw [ext1_comm f (ρ g) (ρ' g) (hf g), this]

theorem fildR_map (f : V →ₗ[LL] V') (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    ∀ x ∈ FildR PD ρ τ a, ext1 Qp BdR f x ∈ FildR PD ρ' τ a := by
  intro x hx
  simp only [FildR, DdRE, DdR, FilV, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero,
    LinearMap.mem_range] at hx ⊢
  obtain ⟨⟨h1, h2⟩, y, hy⟩ := hx
  refine ⟨⟨fun g => ?_, fun c => ?_⟩, ext1 Qp _ f y, ?_⟩
  · have := h1 g
    unfold actVdR at this ⊢
    rw [ext1_comm f (ρ g) (ρ' g) (hf g), this]
  · have := h2 c
    unfold mulVdR at this ⊢
    rw [ext1_comm f LinearMap.id LinearMap.id (fun _ => rfl), this, map_smul]
  · rw [ext1_comm f LinearMap.id LinearMap.id (fun _ => rfl), hy]

theorem finrank_add_tensor {C : Type} [AddCommGroup C] [Module Qp C] (e : V ≃ₗ[LL] (V' × V''))
    (S : Submodule LL (V ⊗[Qp] C)) (S₁ : Submodule LL (V' ⊗[Qp] C)) (S₂ : Submodule LL (V'' ⊗[Qp] C))
    [Module.Finite LL S₁] [Module.Finite LL S₂]
    (a₁ : ∀ x ∈ S, ext1 Qp C (LinearMap.fst LL V' V'' ∘ₗ e.toLinearMap) x ∈ S₁)
    (a₂ : ∀ x ∈ S, ext1 Qp C (LinearMap.snd LL V' V'' ∘ₗ e.toLinearMap) x ∈ S₂)
    (b₁ : ∀ x ∈ S₁, ext1 Qp C (e.symm.toLinearMap ∘ₗ LinearMap.inl LL V' V'') x ∈ S)
    (b₂ : ∀ x ∈ S₂, ext1 Qp C (e.symm.toLinearMap ∘ₗ LinearMap.inr LL V' V'') x ∈ S) :
    finrank LL S = finrank LL S₁ + finrank LL S₂ := by
  refine finrank_add_of_biprod _ _ _ _ ?_ ?_ ?_ ?_ ?_ S S₁ S₂ a₁ a₂ b₁ b₂
  · intro x
    rw [ext1_comp_ext1]
    convert ext1_id (LL := LL) x
    ext v; simp
  · intro x
    rw [ext1_comp_ext1]
    convert ext1_id (LL := LL) x
    ext v; simp
  · intro x
    rw [ext1_comp_ext1]
    convert ext1_zero (LL := LL) x
    ext v; simp
  · intro x
    rw [ext1_comp_ext1]
    convert ext1_zero (LL := LL) x
    ext v; simp
  · intro x
    rw [ext1_comp_ext1, ext1_comp_ext1, ext1_add]
    convert ext1_id (LL := LL) x
    ext v
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      ← map_add]
    apply e.injective
    simp

variable {ρ'' : Representation LL G V''}

theorem equivariant_inl_inr_of_prod_equiv (e : V ≃ₗ[LL] (V' × V''))
    (he : ∀ g v, e (ρ g v) = (ρ' g (e v).1, ρ'' g (e v).2)) :
    (∀ g v, (LinearMap.fst LL V' V'' ∘ₗ e.toLinearMap) (ρ g v) =
      ρ' g ((LinearMap.fst LL V' V'' ∘ₗ e.toLinearMap) v)) ∧
    (∀ g v, (LinearMap.snd LL V' V'' ∘ₗ e.toLinearMap) (ρ g v) =
      ρ'' g ((LinearMap.snd LL V' V'' ∘ₗ e.toLinearMap) v)) ∧
    (∀ g v, (e.symm.toLinearMap ∘ₗ LinearMap.inl LL V' V'') (ρ' g v) =
      ρ g ((e.symm.toLinearMap ∘ₗ LinearMap.inl LL V' V'') v)) ∧
    (∀ g v, (e.symm.toLinearMap ∘ₗ LinearMap.inr LL V' V'') (ρ'' g v) =
      ρ g ((e.symm.toLinearMap ∘ₗ LinearMap.inr LL V' V'') v)) := by
  refine ⟨fun g v => by simp [he], fun g v => by simp [he], fun g v => ?_, fun g v => ?_⟩
  · apply e.injective
    rw [he]; simp
  · apply e.injective
    rw [he]; simp

theorem finite_fildR [Module.Finite LL (DdR PD ρ)] (τ : K →ₐ[Qp] LL) (a : ℤ) :
    Module.Finite LL (FildR PD ρ τ a) :=
  Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) (inf_le_left.trans inf_le_left)

theorem multV_add (e : V ≃ₗ[LL] (V' × V''))
    (he : ∀ g v, e (ρ g v) = (ρ' g (e v).1, ρ'' g (e v).2))
    [Module.Finite LL (DdR PD ρ')] [Module.Finite LL (DdR PD ρ'')] (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD ρ τ a = multV PD ρ' τ a + multV PD ρ'' τ a := by
  obtain ⟨h1, h2, h3, h4⟩ := equivariant_inl_inr_of_prod_equiv e he
  have key : ∀ b, finrank LL (FildR PD ρ τ b) =
      finrank LL (FildR PD ρ' τ b) + finrank LL (FildR PD ρ'' τ b) := fun b => by
    haveI := finite_fildR PD (ρ := ρ') τ b
    haveI := finite_fildR PD (ρ := ρ'') τ b
    exact finrank_add_tensor e _ _ _ (fildR_map PD _ h1 τ b) (fildR_map PD _ h2 τ b)
      (fildR_map PD _ h3 τ b) (fildR_map PD _ h4 τ b)
  simp only [multV, key]
  push_cast
  ring

end Funct

end GlobalTheory.HTW.SumJumps
end
end
