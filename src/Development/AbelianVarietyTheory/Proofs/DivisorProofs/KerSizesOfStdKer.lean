module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLeLOfLeCond
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam recGlob Twist)

namespace GlobalTheory.ColumnNormCompare.SizeRows

variable {D : D7} {large₂ : SizeData₂ D}

theorem one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b Scale.L
  have := s.one_lt_alt
  exact Real.one_le_exp (by positivity)

theorem condE_le_b (P : ParameterChoice' D large₂) : (LevelStarExponents.condE D : ℝ) ≤ large₂.sc.b := by
  have h := P.condE_le
  have hb := one_le_b large₂.sc
  have h1 : large₂.sc.b ^ ((1 : ℝ) / 2) ≤ large₂.sc.b := by
    simpa using Real.rpow_le_rpow_of_exponent_le hb (show (1 : ℝ) / 2 ≤ 1 by norm_num)
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ large₂.t_win.1
  have hc : (LevelStarExponents.condE D : ℝ) ≤ (LevelStarExponents.condE D : ℝ) ^ 36 := by
    exact_mod_cast Nat.le_self_pow (by norm_num) _
  have h2 : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ (LevelStarExponents.condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 :=
    le_mul_of_one_le_right (by positivity) ht
  linarith

theorem log_le_L_of_le_cond (P : ParameterChoice' D large₂) {p : ℕ} (hp : 0 < p) (h : p ≤ LevelStarExponents.condE D) :
    Real.log p ≤ large₂.sc.L := by
  have h1 : (p : ℝ) ≤ Real.exp large₂.sc.L := le_trans (by exact_mod_cast h) (condE_le_b P)
  exact (Real.log_le_iff_le_exp (by exact_mod_cast hp)).2 h1

theorem f_mul_N_le_b (P : ParameterChoice' D large₂) (h4 : 4 * placeRankTwoOne.NN D ^ 3 ≤ large₂.etaSz) :
    (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ≤ large₂.sc.b := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk' : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (0 : ℝ) < D.R.f := by
    have : 0 < D.R.f := by
      have hn : 0 < D.R.n := D.R.ord_pos
      unfold Ranks.f
      omega
    exact_mod_cast this
  have ht := large₂.t_win.1
  have he := large₂.etaSz_pos
  have h := P.eta_le
  rw [le_div_iff₀ (by positivity)] at h
  have hN : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by
    exact_mod_cast Nat.le_self_pow (by norm_num) _
  have hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
  unfold placeRankTwoOne.NN at h4
  have h5 : (D.R.N D.R.m : ℝ) ≤ large₂.etaSz := by linarith
  have h6 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 := one_le_pow₀ ht
  have h7 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hk'
  calc (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) = (D.R.N D.R.m : ℝ) * (1 * D.R.f * 1) := by ring
    _ ≤ large₂.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := by gcongr
    _ ≤ _ := h

theorem eTau_tauPl (z : RPl D.R) : (D.eTau (tauPl D z) : D.R.GG) = G.plGG D z := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]

theorem not_top_of (z : RPl D.R) (hz : ¬ PlaceLogThetaBounds.IsTopPl (numDatumOfParameters D large₂) z) :
    (D.eTau (tauPl D z) : D.R.GG) ∉ D.host.topPlaces := by
  rw [eTau_tauPl]
  intro h
  unfold Host.topPlaces at h
  obtain ⟨t, ht, he⟩ := Finset.mem_image.1 h
  obtain ⟨b, s⟩ := z
  cases b
  · have h1 : D.R.tau1 t = D.R.tau1 s := he
    have h2 : t = s := D.R.toFrame.tau1_injective h1
    subst h2
    exact hz ⟨rfl, ht⟩
  · have h1 : D.R.tau1 t = D.R.tau2 s := he
    exact (factPlaces D.R.toFrame).2 _ _ h1

end GlobalTheory.ColumnNormCompare.SizeRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SizeInequalitiesNoLevelPrimeColumnNormParameters
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPartitionRowsNumericDatumMemIcc
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPartitionRowsNumericDatumMemIcc
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.RowsRangeS

variable {D : D7}

variable {D : D7}

theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b :=
  Real.one_le_exp (by linarith [one_le_scL L])

theorem b'_pos (L : SizeData₂ D) : 0 < L.sc.b' := by
  have := L.sc.one_lt_alt
  have := one_le_b L
  unfold Scale.b' Scale.a Scale.X'
  positivity

theorem one_le_n (D : D7) : (1 : ℝ) ≤ D.R.n := by
  have : 1 ≤ D.R.n := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    unfold Ranks.n
    omega
  exact_mod_cast this

theorem exists_top {τ : D.what₂.Tau} (h : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces) :
    ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t := by
  unfold Host.topPlaces at h
  obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 h
  exact ⟨⟨t, ht⟩, hte.symm⟩

theorem uW_numRec (large₂ : SizeData₂ D) (hD : ∃ n : ℕ, D.s.Del = n) (u : D.what₂.Word) (z : RPl D.R) (i : Fin D.R.k) :
    (numDatumOfParameters D large₂).uW (codeRec large₂ u) z i = (D.hcW u (tauPl D z)).u i := by
  obtain ⟨n, hn⟩ := hD
  obtain ⟨r, hr⟩ := i
  unfold NumDatum.uW
  split_ifs with h h1
  · obtain ⟨l, rfl⟩ : ∃ l, r = l + 1 := ⟨r - 1, by have := h.1; simp only at this; omega⟩
    have h' : l < D.R.k - 2 := by have := h.2; simp only at this; omega
    have a := D.s.u_letter u (tauPl D z) l h'
    have h2 : D.s.letter u ⟨l, h'⟩ = true := h1
    rw [if_pos h2, D.hcW_v] at a
    have h3 : (((numDatumOfParameters D large₂).Del : ℕ) : ℚ) = D.s.Del := by
      show ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del
      rw [hn, Nat.floor_natCast]
    rw [a, h3]
    rfl
  · obtain ⟨l, rfl⟩ : ∃ l, r = l + 1 := ⟨r - 1, by have := h.1; simp only at this; omega⟩
    have h' : l < D.R.k - 2 := by have := h.2; simp only at this; omega
    have a := D.s.u_letter u (tauPl D z) l h'
    have h2 : ¬ D.s.letter u ⟨l, h'⟩ = true := h1
    rw [if_neg h2, D.hcW_v] at a
    rw [a]
    rfl
  · by_cases h0 : r = 0
    · subst h0
      exact (D.hcW_first u _ hr).symm
    · obtain rfl : r = D.R.k - 1 := by simp only at h; omega
      exact (D.hcW_last u _ (by omega)).symm

theorem nu_numRec (large₂ : SizeData₂ D) (hD : ∃ n : ℕ, D.s.Del = n) (u : D.what₂.Word) (j : ℕ) (z : RPl D.R) (i : ℕ) :
    (((numDatumOfParameters D large₂).nu (codeRec large₂ u) j z i : ℚ) : ℝ) = DV.nuRow D u j (tauPl D z) i := by
  have e1 : (numDatumOfParameters D large₂).srcPar (codeRec large₂ u) z i = DV.srcPar D u (tauPl D z) i := by
    unfold NumDatum.srcPar DV.srcPar
    by_cases h : i < D.R.k
    · rw [dite_eq_left h, dite_eq_left h]
      exact uW_numRec large₂ hD u z ⟨i, h⟩
    · rw [dite_eq_right h, dite_eq_right h, D.hcW_e]
  have e2 : (((numDatumOfParameters D large₂).eQ j z : ℚ) : ℝ) = DV.wSz D j (tauPl D z) := by
    unfold NumDatum.eQ DV.wSz
    by_cases h : 1 ≤ j ∧ j ≤ D.R.m
    · rw [dite_eq_left h, dite_eq_left h]
    · rw [dite_eq_right h, dite_eq_right h, Rat.cast_zero]
  unfold NumDatum.nu DV.nuRow
  rw [e1, ← e2]
  push_cast
  rfl

theorem nuRow_zero_le_three_mul (large₂ : SizeData₂ D) (P : ParameterChoice' D large₂) (hb : ∀ t, (large₂.bT t : ℝ) ≤ 2 * large₂.sc.b')
    (hT : ThickUp large₂) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    DV.nuRow D u (i + 1) τ 0 ≤ 3 * large₂.sc.a := by
  have hm := D.R.two_le_m
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk0 : 0 < D.R.k := by omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hkN : (D.R.k : ℝ) ≤ D.R.N i := by
    have : D.R.k ≤ D.R.N i := by unfold Ranks.N; omega
    exact_mod_cast this
  have hx := large₂.sc.one_lt_alt
  have hb1 := one_le_b large₂
  have hb' := b'_pos large₂
  have hba : large₂.sc.b ≤ large₂.sc.a := le_mul_of_one_le_left (by linarith) hx.le
  have hX : 2 ≤ large₂.sc.X' := by
    have h1 : 1 ≤ large₂.sc.x ^ (large₂.sc.eps / 3) := Real.one_le_rpow hx.le (by linarith [large₂.sc.eps_pos])
    have h2 := Real.add_one_le_exp (large₂.sc.x ^ (large₂.sc.eps / 3))
    unfold Scale.X'
    linarith
  have hb'a : large₂.sc.b' ≤ large₂.sc.a / 2 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hX
  have hw : large₂.sc.w'' D.R.n ≤ large₂.sc.b' :=
    div_le_self hb'.le (one_le_mul_of_one_le_of_one_le hx.le (one_le_n D))
  have he := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have heta : 2 * large₂.etaSz ≤ large₂.sc.b' := by
    have h1 : (2 : ℝ) ≤ D.R.m * ((D.R.t : ℝ) + 1) := by nlinarith
    linarith [P.mteta, mul_le_mul_of_nonneg_right h1 he.le]
  have hSc : 5 * large₂.Sc ≤ large₂.sc.b' := by
    linarith [P.kS_le, mul_le_mul_of_nonneg_right hk' hS.le]
  have hwj : wj D (i + 1) τ = (((D.hc τ).e ⟨i, hi⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dite_eq_left (by simpa using hi)]
    rfl
  rw [RowWeightLemmas.nuRow_head D u i hi τ 0 hk0, D.hcW_first u τ hk0, D.hcW_e]
  push_cast
  rw [← hwj]
  by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, htt⟩ := exists_top ha
    rw [(large₂.top_u τ t hk0 htt).1]
    have a1 := (large₂.win_top (i + 1) (by omega) hi τ t htt).2
    have a2 := (large₂.aT_win t).2
    have a3 : (5 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2) :=
      hk'.trans (le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hx.le (by unfold Scale.A; norm_num)))
    have a4 : large₂.sc.a / ((D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2)) ≤ large₂.sc.a / 5 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) a3
    have a5 : large₂.sc.b' / large₂.sc.x ≤ large₂.sc.b' := div_le_self hb'.le hx.le
    linarith [hb t]
  · have h1 := P.cloud_place_bound τ (by omega) ha
    have h2 := (large₂.cloud_v τ ⟨0, by omega⟩).2
    push_cast at h1
    by_cases hc : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have a1 := hT (i + 1) (by omega) hi τ hc
      linarith
    · have a1 := (large₂.win_thin (i + 1) (by omega) hi τ ⟨(D.eTau τ).2, ha, hc⟩).2
      linarith

theorem nu_numRec_mem : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word), ∀ j ∈ (numDatumOfParameters D L).lifts, ∀ z,
    ∀ i < D.R.N (j - 1), 0 ≤ (numDatumOfParameters D L).nu (codeRec L u) j z i ∧
      (((numDatumOfParameters D L).nu (codeRec L u) j z i : ℚ) : ℝ) ≤ 3 * L.sc.a := by
  rintro D large₂ CY ⟨⟨P⟩, -, -, hN, hD, hT⟩ u j hj z r hr
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m := j2
  have hr' : r < D.R.N i := hr
  have e := nu_numRec large₂ hD u (i + 1) z r
  constructor
  · have h := (RowWeightLemmas.nuRow_pos D u i hi (tauPl D z) r hr').le
    rw [← e] at h
    exact_mod_cast h
  · rw [e]
    exact (RowWeightLemmas.nuRow_anti' D u i hi _ r 0 (Nat.zero_le _) hr').trans
      (nuRow_zero_le_three_mul large₂ P hN.2.2.2.2 hT u i hi _)

end GlobalTheory.CoreHt.RowsRangeS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPartitionRowsNumericDatumMemIccStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPartitionRows_numericDatum_mem_Icc : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word), ∀ j ∈ (numDatumOfParameters D L).lifts, ∀ z, ∀ i < D.R.N (j - 1), 0 ≤ (numDatumOfParameters D L).nu (codeRec L u) j z i ∧ (((numDatumOfParameters D L).nu (codeRec L u) j z i : ℚ) : ℝ) ≤ 3 * L.sc.a := by
  first | exact @GlobalTheory.CoreHt.RowsRangeS.nu_numRec_mem | exact GlobalTheory.CoreHt.RowsRangeS.nu_numRec_mem | (intros; apply GlobalTheory.CoreHt.RowsRangeS.nu_numRec_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SizeInequalitiesNoLevelPrimeColumnNormParameters
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.SizeRowsRec

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColumnNormCompare.SizeRows

theorem sizeRowsS_numRec : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word),
    SizeRowsS CY (numDatumOfParameters D L) (codeRec L u) := by
  intro D large₂ CY hR u
  have hnu := GlobalTheory.T.fockPartitionRows_numericDatum_mem_Icc D large₂ CY hR u
  obtain ⟨⟨P⟩, ⟨s2, s3, s4⟩, hg, ⟨s10, -, -, -, s14⟩, ⟨n, hn⟩, -⟩ := hR
  have hDel : ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del := by rw [hn, Nat.floor_natCast]
  have hSc : (numDatumOfParameters D large₂).Sc = large₂.Sc := by
    rw [large₂.Sc_eq]
    show (D.R.k : ℝ) * (4 * ((⌊D.s.Del⌋₊ : ℕ) : ℝ)) = _
    rw [← Rat.cast_natCast, ← Rat.cast_natCast (α := ℝ) ⌊D.s.Del⌋₊, hDel]
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hm : (0 : ℝ) < D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 0 < D.R.m)
  have hn0 : 0 < D.R.n := D.R.n_pos'
  have hq := D.host.hyp.1.pos
  have hd := D.host.hyp.2.1.pos
  refine ⟨⟨?_, ?_, ?_, s4, ?_⟩, fun i => ⟨?_, hg i⟩, trivial, f_mul_N_le_b P s10, hnu, ?_, ?_, ?_, ?_, ?_⟩
  · exact s2
  · refine log_le_L_of_le_cond P hq ?_
    unfold LevelStarExponents.condE
    exact le_trans (Nat.le_mul_of_pos_left _ D.host.QS_pos) (Nat.le_mul_of_pos_right _ hd)
  · refine log_le_L_of_le_cond P hd ?_
    unfold LevelStarExponents.condE
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos D.host.QS_pos hq)
  · rw [large₂.logDerivative_at_one_eq] at s3
    exact s3
  · obtain ⟨Y, h1, -, -, h2⟩ := P.g_Y
    exact h1.trans (h2 i).1
  · intro z i j
    refine (large₂.be_close (tauPl D z) i j).trans ?_
    show large₂.etaSz ≤ (D.R.m : ℝ) * ((⌈LevelStarExponents.h0 large₂⌉₊ : ℕ) : ℝ)
    have h := Nat.le_ceil (LevelStarExponents.h0 large₂)
    calc large₂.etaSz = (D.R.m : ℝ) * LevelStarExponents.h0 large₂ := by unfold LevelStarExponents.h0; field_simp
      _ ≤ _ := by gcongr
  · intro z i
    rw [hSc]
    obtain ⟨h1, h2⟩ := large₂.cloud_v (tauPl D z) i
    exact ⟨by exact_mod_cast h1, h2⟩
  · intro z i h1 h2
    obtain ⟨i, hi⟩ := i
    obtain ⟨l, rfl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by simp only at h1; omega⟩
    have hl : l < D.R.k - 2 := by
      have : l + 1 + 1 < D.R.k := h2
      omega
    have e : (numDatumOfParameters D large₂).uW (codeRec large₂ u) z ⟨l + 1, hi⟩ = (D.hcW u (tauPl D z)).u ⟨l + 1, hi⟩ := by
      rw [D.s.u_letter u (tauPl D z) l hl, D.hcW_v]
      unfold NumDatum.uW
      rw [dite_eq_left ⟨h1, h2⟩]
      show _ - _ - (if D.s.letter u ⟨l, hl⟩ = true then ((⌊D.s.Del⌋₊ : ℕ) : ℚ) else 0) = _
      rw [hDel]
      rfl
    rw [hSc, e]
    obtain ⟨a1, a2⟩ := large₂.cloud_u u (tauPl D z) ⟨l + 1, hi⟩ h1 h2
    exact ⟨by exact_mod_cast a1, a2⟩
  · intro t ht
    have h := (large₂.top_u (tauPl D (false, t)) ⟨t, ht⟩ (by omega) (eTau_tauPl (false, t))).2
    have e : (((numDatumOfParameters D large₂).bT t : ℚ) : ℝ) = (large₂.bT ⟨t, ht⟩ : ℝ) := by
      unfold NumDatum.bT
      push_cast
      erw [h]
      ring
    rw [e]
    exact ⟨large₂.bT_ge _, s14 _⟩
  · intro z hz hk2
    have hz' := not_top_of z hz
    rw [hSc]
    refine ⟨P.uk_extreme _ hk2 hz', (large₂.cloud_gap _ (by omega) hz').1, ?_⟩
    have h1 := P.cloud_place_bound _ (by omega) hz'
    have h2 := (large₂.cloud_v (tauPl D z) ⟨0, by omega⟩).2
    push_cast at h1
    show (((D.hc (tauPl D z)).u ⟨0, by omega⟩ : ℚ) : ℝ) ≤ _
    linarith

end GlobalTheory.CoreHt.SizeRowsRec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SizeInequalitiesNoLevelPrimeColumnNormParametersStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizeInequalitiesNoLevelPrime_columnNormParameters : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word), SizeRowsS CY (numDatumOfParameters D L) (codeRec L u) := by
  first | exact @GlobalTheory.CoreHt.SizeRowsRec.sizeRowsS_numRec | exact GlobalTheory.CoreHt.SizeRowsRec.sizeRowsS_numRec | (intros; apply GlobalTheory.CoreHt.SizeRowsRec.sizeRowsS_numRec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsPrimeWeightSizes
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WtsOkAndSizes
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem

theorem wts_ok_and_sizes :
    ∀ (B : Base) (X : PreX B.toPre), B.wts.Ok ∧ Sizes (B.primes X) B.wts X.a :=
  fun B X => ⟨B.wts_isOk, B.primes_sizes X⟩

end GlobalTheory.Mem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnWeightSpreadLeTwoMulScale
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnWeightSpreadLeTwoMulScale
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.SpreadBound

theorem spread_lamOf_le {R : Ranks} (p : HCParam R) (j : ℕ) (hj : j ≤ R.m) (hk : 0 < R.k) (hm : R.m - 1 < R.m) :
    (((Formalism.BasicNotions.Examples₂.lamOf p j).spread : ℤ) : ℚ) ≤ p.u ⟨0, hk⟩ + p.e ⟨R.m - 1, hm⟩ + R.N R.m := by
  have hN : 0 < R.N j := by unfold Ranks.N; omega
  have hNm := Formalism.BasicNotions.Examples₂.N_mono (R := R) hj
  have h2 := R.two_le_m
  unfold DomWeight.spread
  rw [dite_eq_left hN]
  push_cast
  rw [Formalism.BasicNotions.Examples₂.lamOf_eq p j hj, Formalism.BasicNotions.Examples₂.lamOf_eq p j hj, Formalism.BasicNotions.Examples₂.wtQ_eq_wtN, Formalism.BasicNotions.Examples₂.wtQ_eq_wtN]
  have a1 : Formalism.BasicNotions.Examples₂.wtN p (R.N R.m - 1) ≤ Formalism.BasicNotions.Examples₂.wtN p (R.N j - 1) :=
    Formalism.BasicNotions.Examples₂.wtN_anti p (by omega) (by omega)
  have hmul : R.m * (R.t + 1) = (R.m - 1) * (R.t + 1) + (R.t + 1) := by
    obtain ⟨n, hn⟩ : ∃ n, R.m = n + 1 := ⟨R.m - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel]; ring
  have hb : Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) = R.m - 1 := by
    unfold Formalism.BasicNotions.Examples₂.blkN Ranks.N
    have : R.k + R.m * (R.t + 1) - 1 - R.k = R.t + (R.t + 1) * (R.m - 1) := by
      rw [hmul, mul_comm (R.t + 1)]; omega
    rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  have a2 : -p.e ⟨R.m - 1, hm⟩ ≤ Formalism.BasicNotions.Examples₂.wtN p (R.N R.m - 1) := by
    have c1 : ¬ R.N R.m - 1 < R.k := by unfold Ranks.N; omega
    have c2 : Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) < R.m := by omega
    unfold Formalism.BasicNotions.Examples₂.wtN
    rw [dite_eq_right c1, dite_eq_left c2]
    have e : (⟨Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1), c2⟩ : Fin R.m) = ⟨R.m - 1, hm⟩ := Fin.ext hb
    rw [e]
    unfold wG
    push_cast
    have : (0 : ℚ) ≤ (2 * ((Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) : ℚ) + 1) - 1) * ((R.t : ℚ) + 1) / 2 := by
      have : (0 : ℚ) ≤ 2 * ((Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) : ℚ) + 1) - 1 := by
        have : (0 : ℚ) ≤ (Formalism.BasicNotions.Examples₂.blkN R (R.N R.m - 1) : ℚ) := by positivity
        linarith
      positivity
    have : (0 : ℚ) ≤ (R.k : ℚ) / 2 := by positivity
    linarith
  have a3 : Formalism.BasicNotions.Examples₂.wtN p 0 ≤ p.u ⟨0, hk⟩ := by
    unfold Formalism.BasicNotions.Examples₂.wtN
    rw [dite_eq_left hk]
    unfold hcToWeightQ rhoVec
    have : (1 : ℚ) ≤ R.k := by exact_mod_cast hk
    simp only [Nat.cast_zero]
    linarith
  have a4 : (R.N j : ℚ) ≤ R.N R.m := by exact_mod_cast hNm
  simp only
  linarith

end GlobalTheory.CoreHt.SpreadBound

namespace GlobalTheory.CoreHt.SpreadBound

theorem spread_lamTrue_le : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (L : SizeData₂ (I.rec7 l Z)) (CY : ℝ), HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → ∀ (u : B.Word) (j : ℕ), j ≤ B.R.m → ∀ τ,
    ((B.wts.lamTrue u j τ).spread : ℝ) ≤ 2 * L.sc.a := by
  intro B X I _ l Z L CY hS hX hx u j hj τ
  obtain ⟨⟨P⟩, -, -, ⟨hN3, -, hmt, hkS, hbT⟩, -, hT⟩ := hS
  have hm := B.R.two_le_m
  have hk : 5 ≤ B.R.k := by have := B.R.m_add_three_le_k; omega
  have hk0 : 0 < B.R.k := by omega
  have hm1 : B.R.m - 1 < B.R.m := by omega
  have c1 := spread_lamOf_le (B.hcW u τ) j hj hk0 hm1
  have c2 : (((B.wts.lamTrue u j τ).spread : ℤ) : ℝ) ≤
      (((B.hcW u τ).u ⟨0, hk0⟩ : ℚ) : ℝ) + (((B.hcW u τ).e ⟨B.R.m - 1, hm1⟩ : ℚ) : ℝ) + B.R.N B.R.m := by
    unfold Wts.lamTrue
    rw [spread_shiftW]
    exact_mod_cast c1
  refine c2.trans ?_
  have hx1 := L.sc.one_lt_alt
  have hL1 : 1 ≤ L.sc.L := Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (by linarith)
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have hb2 : 2 * L.sc.b ≤ L.sc.a := by rw [ha]; nlinarith
  have hX0 : 0 < L.sc.X' := by linarith
  have hb'a : L.sc.b' ≤ L.sc.a / 8 := by
    have : 0 < L.sc.a := by linarith
    exact div_le_div_of_nonneg_left this.le (by norm_num) hX
  have hb'0 : 0 < L.sc.b' := by
    have : 0 < L.sc.a := by linarith
    exact div_pos this hX0
  have hn1 : (1 : ℝ) ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.n := by
    have : 1 ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.n := by
      have h₁ := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.two_le_m
      have h₂ := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m_le_f
      unfold Ranks.n
      omega
    exact_mod_cast this
  have hw : L.sc.w'' (I.rec7 l Z).R.n ≤ L.sc.b' :=
    div_le_self hb'0.le (one_le_mul_of_one_le_of_one_le hx1.le hn1)
  have he := L.etaSz_pos
  have hS0 := L.Sc_pos
  have hm' : (2 : ℝ) ≤ B.R.m := by exact_mod_cast hm
  have hk' : (5 : ℝ) ≤ B.R.k := by exact_mod_cast hk
  have ht : (0 : ℝ) ≤ B.R.t := Nat.cast_nonneg _
  have heta : 2 * L.etaSz ≤ L.sc.b' := by
    have h1 : (2 : ℝ) ≤ B.R.m * ((B.R.t : ℝ) + 1) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 he.le
    have h3 : (B.R.m : ℝ) * ((B.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' (I.rec7 l Z).R.n := hmt
    linarith
  have hSc : 5 * L.Sc ≤ L.sc.b' := by
    have h3 : (B.R.k : ℝ) * L.Sc ≤ L.sc.w'' (I.rec7 l Z).R.n := hkS
    nlinarith
  have hN1 : (1 : ℝ) ≤ B.R.N B.R.m := by
    have : 1 ≤ B.R.N B.R.m := by unfold Ranks.N; omega
    exact_mod_cast this
  have hNeta : (B.R.N B.R.m : ℝ) ≤ L.etaSz := by
    have h3 : 4 * (B.R.N B.R.m : ℝ) ^ 3 ≤ L.etaSz := hN3
    have h4 : (B.R.N B.R.m : ℝ) ^ 1 ≤ (B.R.N B.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN1 (by norm_num)
    rw [pow_one] at h4
    linarith
  have hkN : (B.R.k : ℝ) ≤ B.R.N B.R.m := by
    have : B.R.k ≤ B.R.N B.R.m := by unfold Ranks.N; omega
    exact_mod_cast this
  have hu0 : (B.hcW u τ).u ⟨0, hk0⟩ = ((I.rec7 l Z).hc τ).u ⟨0, hk0⟩ := (I.rec7 l Z).hcW_first u τ hk0
  have he0 : (B.hcW u τ).e = ((I.rec7 l Z).hc τ).e := (I.rec7 l Z).hcW_e u τ
  have hwm : wj (I.rec7 l Z) B.R.m τ = (((B.hcW u τ).e ⟨B.R.m - 1, hm1⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dite_eq_left (show B.R.m - 1 < (I.rec7 l Z).R.m from hm1)]
    exact (congrArg (fun f => ((f ⟨B.R.m - 1, hm1⟩ : ℚ) : ℝ)) he0).symm
  rw [← hwm, hu0]
  by_cases htop : ((I.rec7 l Z).eTau τ : (I.rec7 l Z).R.GG) ∈ (I.rec7 l Z).host.topPlaces
  · obtain ⟨t, htt⟩ : ∃ t : (I.rec7 l Z).host.TT,
        ((I.rec7 l Z).eTau τ : (I.rec7 l Z).R.GG) = (I.rec7 l Z).R.tau1 t := by
      unfold Host.topPlaces at htop
      obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htop
      exact ⟨⟨t, ht⟩, hte.symm⟩
    rw [(L.top_u τ t hk0 htt).1]
    show (L.aT t : ℝ) + ((B.R.k : ℝ) - 1) / 2 + wj (I.rec7 l Z) B.R.m τ + (B.R.N B.R.m : ℝ) ≤ 2 * L.sc.a
    have a1 : wj (I.rec7 l Z) B.R.m τ ≤ (L.bT t : ℝ) + L.sc.b' / L.sc.x + L.etaSz :=
      (L.win_top B.R.m (by omega) le_rfl τ t htt).2
    have a2 : (L.aT t : ℝ) ≤ L.sc.a + L.sc.a / ((B.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) := (L.aT_win t).2
    have a3 : (5 : ℝ) ≤ (B.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) :=
      hk'.trans (le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hx1.le (by unfold Scale.A; norm_num)))
    have a4 : L.sc.a / ((B.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) a3
    have a5 : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hx1.le
    have a6 := hbT t
    linarith
  · have h1 := P.cloud_place_bound τ (by show 0 < B.R.k - 1; omega) htop
    have h2 := (L.cloud_v τ ⟨0, by show 0 < B.R.k - 1; omega⟩).2
    push_cast at h1
    by_cases hc : ((I.rec7 l Z).eTau τ : (I.rec7 l Z).R.GG) ∈ (I.rec7 l Z).host.thickPlaces
    · have a1 := hT B.R.m (by omega) le_rfl τ hc
      linarith
    · have a1 := (L.win_thin B.R.m (by omega) le_rfl τ ⟨((I.rec7 l Z).eTau τ).2, htop, hc⟩).2
      linarith

end GlobalTheory.CoreHt.SpreadBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnWeightSpreadLeTwoMulScaleStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumnWeight_spread_le_two_mul_scale : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (CY : ℝ), HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → ∀ (u : B.Word) (j : ℕ), j ≤ B.R.m → ∀ τ, ((B.wts.lamTrue u j τ).spread : ℝ) ≤ 2 * L.sc.a := by
  first | exact @GlobalTheory.CoreHt.SpreadBound.spread_lamTrue_le | exact GlobalTheory.CoreHt.SpreadBound.spread_lamTrue_le | (intros; apply GlobalTheory.CoreHt.SpreadBound.spread_lamTrue_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsPrimeWeightSizes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem GlobalTheory.CoreHt.sizes_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (CY : ℝ), HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → (∀ u, 4 * L.sc.a < (((I.rec7 l Z).mem u).A.T : ℝ)) → Formalism.L2.Col.Sizes (B.primes X) B.wts L.sc.a := by
  intro B X I h l Z L CY hR hX' hx hT
  have hW := (GlobalTheory.Mem.wts_ok_and_sizes B X).2
  have hF := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).2
  obtain ⟨P⟩ := hR.1
  have hfN := GlobalTheory.ColumnNormCompare.SizeRows.f_mul_N_le_b P hR.2.2.2.1.1
  have hb1 := GlobalTheory.ColumnNormCompare.SizeRows.one_le_b L.sc
  refine ⟨hW.g_big, fun u => hT u, ?_, GlobalTheory.T.trueColumnWeight_spread_le_two_mul_scale I h l Z L CY hR hX' hx⟩
  have hab : 2 * L.sc.b ≤ L.sc.a := by
    show 2 * L.sc.b ≤ L.sc.x * L.sc.b
    nlinarith
  have hfN' : ((B.fields.f : ℝ)) * (B.R.N B.R.m : ℝ) ≤ L.sc.b := by
    rw [hF]; exact hfN
  push_cast
  linarith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsPrimeWeightSizesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumns_prime_weight_sizes : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (CY : ℝ), HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → (∀ u, 4 * L.sc.a < (((I.rec7 l Z).mem u).A.T : ℝ)) → Formalism.L2.Col.Sizes (B.primes X) B.wts L.sc.a := by
  first | exact @GlobalTheory.CoreHt.sizes_trueCols | exact GlobalTheory.CoreHt.sizes_trueCols | (intros; apply GlobalTheory.CoreHt.sizes_trueCols <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColRows


set_option maxHeartbeats 800000 in
theorem kerSizes_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → ∀ CY CT : ℝ, GlobalTheory.CoreHt.HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → (∀ u, 4 * L.sc.a < (((I.rec7 l Z).mem u).A.T : ℝ)) → (∀ u, Real.log ((((I.rec7 l Z).mem u).A.T : ℕ) : ℝ) ≤ CT * (I.rec7 l Z).R.m * L.sc.L) → GlobalTheory.ColRows.KerSizes t W Del h0 CY CT := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW hDel hEta CY CT hH hX' hx hTa hlogT
  have hNum := GlobalTheory.T.columnNormParameters_eq_natStepGap (I.rec7 l Z) L Del h0 hDel hEta
  have hSz := GlobalTheory.T.trueColumns_prime_weight_sizes I hOk l Z L CY hH hX' hx hTa
  refine ⟨?_, ?_, hlogT⟩
  · obtain ⟨hX, -, hPr, -⟩ := hS
    cases t
    dsimp only at hX hPr W hW ⊢
    subst hX
    cases eq_of_heq hPr
    cases eq_of_heq hW
    exact hSz
  · intro u
    have h := GlobalTheory.T.sizeInequalitiesNoLevelPrime_columnNormParameters (I.rec7 l Z) L CY hH u
    unfold GlobalTheory.ColumnNormCompare.codeRec at h
    convert h using 1 <;> first | exact hNum.symm | exact HEq.rfl | rfl

end GlobalTheory.ColRows
