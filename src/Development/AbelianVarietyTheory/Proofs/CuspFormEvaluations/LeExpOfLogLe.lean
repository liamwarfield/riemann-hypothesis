module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueExistsUniqueNaturalOfLaws
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeExpOfLogLe
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.LogSupMultiple

theorem le_exp_of_log_le {x b : ℝ} (h : Real.log x ≤ b) (hx : 0 ≤ x) : x ≤ Real.exp b := by
  rcases hx.eq_or_lt with rfl | hpos
  · exact (Real.exp_pos b).le
  · exact (Real.log_le_iff_le_exp hpos).1 h

theorem log_le_of_le_exp {x b : ℝ} (h : x ≤ Real.exp b) (hx : 0 ≤ x) (hb : 0 ≤ b) : Real.log x ≤ b := by
  rcases hx.eq_or_lt with rfl | hpos
  · simpa using hb
  · exact (Real.log_le_iff_le_exp hpos).2 h

theorem supN_sum_le {D : D7} (B : WeightFamilies.Prov D) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : B.KO →+* ℂ) {ι : Type}
    (s : Finset ι) (F : ι → B.Cusp j w) :
    B.supN j w σ (∑ i ∈ s, F i) ≤ ∑ i ∈ s, B.supN j w σ (F i) :=
    Finset.le_sum_of_subadditive (B.supN j w σ) (le_of_eq ((B.supN_eq_zero j w σ 0).2 rfl))
      (B.supN_add j w σ) s F

theorem log_supN_bounds : ∀ (D : D7) (B : WeightFamilies.Prov D) (j : ℕ) (w : WeightFamilies.Wt D j), (∀ (σ : B.KO →+* ℂ) (s : B.KO) (F : B.Cusp j w) (a b : ℝ), 0 ≤ a + b → Real.log ‖σ s‖ ≤ a → Real.log (B.supN j w σ F) ≤ b → 0 ≤ b → 0 ≤ a → Real.log (B.supN j w σ (s • F)) ≤ a + b) ∧ (∀ (σ : B.KO →+* ℂ) (N : ℕ) (c : Fin N → ℕ) (F : Fin N → B.Cusp j w) (b : ℝ), 0 ≤ b → (∀ i, c i ≤ N) → (∀ i, Real.log (B.supN j w σ (F i)) ≤ b) → Real.log (B.supN j w σ (∑ i, (c i : B.KO) • F i)) ≤ 2 * Real.log N + b) ∧ ∀ b : ℝ, (∑ _σ : B.KO →+* ℂ, b) / (Fintype.card (B.KO →+* ℂ) : ℝ) = b := by
  intro D B j w
  refine ⟨?_, ?_, ?_⟩
  ·
    intro σ s F a b _ hs hF hb ha
    rw [B.supN_smul]
    have hF0 := B.supN_nonneg j w σ F
    have h1 : ‖σ s‖ ≤ Real.exp a := le_exp_of_log_le hs (norm_nonneg _)
    have h2 : B.supN j w σ F ≤ Real.exp b := le_exp_of_log_le hF hF0
    refine log_le_of_le_exp ?_ (mul_nonneg (norm_nonneg _) hF0) (add_nonneg ha hb)
    rw [Real.exp_add]
    exact mul_le_mul h1 h2 hF0 (Real.exp_pos a).le
  ·
    intro σ N c F b hb hc hF
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [Fin.sum_univ_zero, (B.supN_eq_zero j w σ 0).2 rfl]
      simpa using hb
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hNpos : (0 : ℝ) < N := by linarith
      have hsum : B.supN j w σ (∑ i, (c i : B.KO) • F i) ≤ (N : ℝ) * ((N : ℝ) * Real.exp b) :=
        calc B.supN j w σ (∑ i, (c i : B.KO) • F i)
            ≤ ∑ i, B.supN j w σ ((c i : B.KO) • F i) := supN_sum_le B j w σ _ _
          _ ≤ ∑ _i : Fin N, (N : ℝ) * Real.exp b := by
            apply Finset.sum_le_sum
            intro i _
            rw [B.supN_smul, map_natCast, Complex.norm_natCast]
            exact mul_le_mul (by exact_mod_cast hc i) (le_exp_of_log_le (hF i) (B.supN_nonneg _ _ _ _))
              (B.supN_nonneg _ _ _ _) hNpos.le
          _ = (N : ℝ) * ((N : ℝ) * Real.exp b) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hexp : Real.exp (2 * Real.log N + b) = (N : ℝ) * ((N : ℝ) * Real.exp b) := by
        rw [Real.exp_add, two_mul, Real.exp_add, Real.exp_log hNpos]
        ring
      refine log_le_of_le_exp ?_ (B.supN_nonneg _ _ _ _) ?_
      · rw [hexp]
        exact hsum
      · have := Real.log_nonneg hN1
        linarith
  ·
    intro b
    have hcard : (Fintype.card (B.KO →+* ℂ) : ℝ) ≠ 0 := by
      have : 0 < Fintype.card (B.KO →+* ℂ) := Fintype.card_pos
      exact_mod_cast this.ne'
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_div_cancel_left₀ b hcard

end GlobalTheory.LogSupMultiple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SizePageRowsOfSizePageAt
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SizePageRowsOfSizePageAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem pageRows_of_pageAt : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → PageAt large₂ C2 A2 → 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka ∧ 16 ≤ D.R.f := by
  intro D B P j X large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp hPg hCK
  have hm4 := EtaleWeightGaps.lift_index_pow_four_le_degree hPg
  obtain ⟨Q, PT, -, hC, hA⟩ := hPg
  have hPP : WeightFamilies.PPv D large₂ C2 A2 = PT.PP := by rw [← hC, ← hA]; exact WeightFamilies.PPv_rec PT
  obtain ⟨hA', hS, -, h4, -⟩ := hp
  obtain ⟨-, -, -, -, hg, -, -, hp1, hp2, -⟩ := hA'
  obtain ⟨hn, -, -, -, -, -, -, hsz, -, -, -, -, -, -, -, -, -, hT, -⟩ := hS
  obtain ⟨-, -, -, hP3, -⟩ := h4
  rw [hPP] at hCK hP3
  have hL := EtaleWeightGaps.Num.Pm.one_le_L large₂
  have hf2 := EtaleWeightGaps.Num.Pm.two_le_f D
  have hr6 := EtaleWeightGaps.Num.Pm.six_le_r D
  have hm2 := EtaleWeightGaps.Num.Pm.two_le_m D
  have hkr := EtaleWeightGaps.Num.Pm.k_le_r D
  have hrt := EtaleWeightGaps.Num.Pm.r_le_alt_alt D
  have hlf := EtaleWeightGaps.Num.Pm.log_f_le Q
  have hlr := EtaleWeightGaps.Num.Pm.log_r_le Q
  obtain ⟨hlc, hlt⟩ := EtaleWeightGaps.Num.Pm.log_cond_le Q
  have hb : Real.log large₂.sc.b = large₂.sc.L := EtaleWeightGaps.Num.Pm.log_b large₂
  have hb0 : 0 < large₂.sc.b := Real.exp_pos _
  have hf0 : (0 : ℝ) < D.R.f := by linarith
  have hr0 : (0 : ℝ) < D.R.r := by linarith
  have hP0 : 0 < PT.PP := PT.PP_pos (by unfold zBase; positivity)
  refine ⟨⟨hg, ?_, ?_, ?_, ?_, hp1, hp2, ?_, ?_⟩, ?_⟩
  · rw [EtaleWeightGaps.Num.Pm.lrd_eq]; linarith [log_rdE_le_scL Q]
  · have hd := EtaleWeightGaps.Num.Pm.one_le_d D
    have hq := EtaleWeightGaps.Num.Pm.one_le_q D
    have h1 : (D.host.d : ℝ) ≤ (LevelStarExponents.condE D : ℝ) := by
      rw [EtaleWeightGaps.Num.Pm.condE_cast]
      have hS : (1 : ℝ) ≤ (D.host.QS : ℝ) := by exact_mod_cast D.host.QS_pos
      have : (1 : ℝ) ≤ (D.host.QS : ℝ) * D.host.q := by nlinarith
      nlinarith
    linarith [Real.log_le_log (by linarith) h1]
  · linarith [Q.ccK_log]
  · linarith
  · have hs : 1 + (WeightAlgebra.DF ka : ℝ) ≤ ka.size := by
      unfold WeightFamilies.Wt.size WeightAlgebra.DF degP
      have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (ka.n : ℝ) := by positivity
      push_cast at h2 ⊢
      linarith
    have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have hT1 : (1 : ℝ) ≤ (Tn : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hT)
    have hP3' : PT.PP ^ 3 ≤ large₂.sc.b := (le_mul_of_one_le_right (by positivity) hT1).trans hP3
    have hlP : 3 * Real.log PT.PP ≤ large₂.sc.L := by
      have := Real.log_le_log (by positivity) hP3'
      rw [Real.log_pow, hb] at this
      exact_mod_cast this
    have h1 : H.CK ≤ PT.PP ^ 2 * D.R.f := by
      have : 0 ≤ PT.PP ^ 2 * D.R.f := by positivity
      linarith
    have h2 : H.CK * D.R.k ≤ PT.PP ^ 2 * D.R.f * D.R.r := mul_le_mul h1 hkr hk0 (by positivity)
    have h3 : H.CK * D.R.k * D.R.f * large₂.sc.b ≤ PT.PP ^ 2 * D.R.f * D.R.r * D.R.f * large₂.sc.b := by gcongr
    have h4 := Real.log_le_log (by positivity) (hs.trans (hsz.trans h3))
    rw [Real.log_mul (by positivity) hb0.ne', Real.log_mul (by positivity) hf0.ne',
      Real.log_mul (by positivity) hr0.ne', Real.log_mul (by positivity) hf0.ne', Real.log_pow, hb] at h4
    push_cast at h4
    linarith
  · have h1 : (ka.n : ℝ) ≤ (D.R.t : ℝ) ^ 2 := by
      rw [hn]; unfold Ranks.nV; push_cast; nlinarith
    have h2 : (0 : ℝ) < ka.n := by rw [hn]; unfold Ranks.nV; push_cast; linarith
    have h3 := Real.log_le_log h2 h1
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  · have : (2 : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hm2 4
    have h : (16 : ℝ) ≤ D.R.f := by linarith
    exact_mod_cast h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SizePageRowsOfSizePageAtStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizePageRows_of_sizePageAt : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → PageAt large₂ C2 A2 → 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka ∧ 16 ≤ D.R.f := by
  first | exact @GlobalTheory.pageRows_of_pageAt | exact GlobalTheory.pageRows_of_pageAt | (intros; apply GlobalTheory.pageRows_of_pageAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupBoundsLeGeneratorConstantMulSize
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupBoundsLeGeneratorConstantMulSize
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem gc_arith (f r L A n s lam lp a b M : ℝ) (hf : 2 ≤ f) (hr : 6 ≤ r) (hL : 2 ≤ L) (hA : 0 ≤ A)
    (hn : 1 ≤ n) (hs : A + f * r * n + 1 ≤ s) (hlam : 0 ≤ lam) (hlp : 0 ≤ lp) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM : a + b ≤ M) :
    (140 * r * L * A + 10 * L * A + 200 * f * r * n * L ≤ 400 * (f * r * L) * s) ∧
    (2 * (lam + 2 * lp) * s + 400 * (f * r * L) * s + lam * s ≤
      (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s) ∧
    ((lam + 2 * lp) * s + (400 * (f * r * L) * s + 3 * f * r * n * L + 5 * a + b + 2) ≤
      (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s) := by
  have hfr : 12 ≤ f * r := by nlinarith
  have hrf : r ≤ f * r := by nlinarith
  obtain ⟨F, hF⟩ : ∃ F, F = f * r := ⟨_, rfl⟩
  rw [← hF] at hfr hrf hs
  have hFn : F ≤ F * n := by nlinarith
  have hnF : n ≤ F * n := by nlinarith
  have hs3 : 13 ≤ s := by linarith
  have hAs : A ≤ s := by linarith
  have hns : n ≤ s := by linarith
  have hFns : F * n ≤ s := by linarith
  have hZ : 24 ≤ F * L := by nlinarith
  have hLZ : L ≤ F * L := by nlinarith
  have hrL : r * L ≤ F * L := by nlinarith
  have hZs : 24 ≤ F * L * s := by nlinarith
  have h1 : r * L * A ≤ F * L * s := mul_le_mul hrL hAs hA (by linarith)
  have h2 : L * A ≤ F * L * s := mul_le_mul hLZ hAs hA (by linarith)
  have h3 : F * L * n ≤ F * L * s := mul_le_mul_of_nonneg_left hns (by linarith)
  have hLs : 0 ≤ L * s := by positivity
  have hM0 : 0 ≤ M := by linarith
  have hMs : M * 13 ≤ M * s := mul_le_mul_of_nonneg_left hs3 hM0
  have hlams : 0 ≤ lam * s := by positivity
  have hlps : 0 ≤ lp * s := by positivity
  have h4 : 12 * (lam * s) ≤ F * (lam * s) := mul_le_mul_of_nonneg_right hfr hlams
  have h5 : 12 * (lp * s) ≤ F * (lp * s) := mul_le_mul_of_nonneg_right hfr hlps
  have e : (1009 * (f * r * L) + (3 * L + 2 * M) + 2 * f * r * (lam + 2 * lp) + 31 * (f * r * L)) * s =
      1040 * (F * L * s) + 3 * (L * s) + 2 * (M * s) + 2 * (F * (lam * s)) + 4 * (F * (lp * s)) := by
    rw [hF]; ring
  have e1 : 400 * (f * r * L) * s = 400 * (F * L * s) := by rw [hF]; ring
  have e2 : 200 * f * r * n * L = 200 * (F * L * n) := by rw [hF]; ring
  have e3 : 3 * f * r * n * L = 3 * (F * L * n) := by rw [hF]; ring
  have e4 : 140 * r * L * A = 140 * (r * L * A) := by ring
  have e5 : 10 * L * A = 10 * (L * A) := by ring
  have e6 : 2 * (lam + 2 * lp) * s = 2 * (lam * s) + 4 * (lp * s) := by ring
  have e7 : (lam + 2 * lp) * s = lam * s + 2 * (lp * s) := by ring
  rw [e, e1, e2, e3, e4, e5, e6, e7]
  refine ⟨by linarith, by linarith, by linarith⟩

theorem lamStar_nonneg_nat (D : D7) : 0 ≤ lamStar D := by
  unfold lamStar
  have h1 : 0 ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := by
    have := Real.log_natCast_nonneg (D.host.g 0 * D.host.g 1)
    simpa only [Nat.cast_mul] using this
  have h2 : 0 ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) := by
    have := Real.log_natCast_nonneg (D.R.f ^ 2 * D.host.q * D.host.d)
    have e : 4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d =
        ((D.R.f ^ 2 * D.host.q * D.host.d : ℕ) : ℝ) := by push_cast; ring
    rw [e]; exact this
  linarith

theorem sup_bounds_le_Gc : ∀ (D : D7) (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j) (p : ℕ), 2 ≤ large₂.sc.L → 0 < w.n → (140 * D.R.r * large₂.sc.L * absA w + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L ≤ 400 * Zb D large₂ * w.size) ∧ (2 * (lamStar D + 2 * Real.log p) * w.size + 400 * Zb D large₂ * w.size + lamStar D * w.size ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) ∧ ((lamStar D + 2 * Real.log p) * w.size + (400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ B.KO) + Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO + 2) ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) := by
  intro D B large₂ j w p hL hn
  have hf : (2 : ℝ) ≤ D.R.f := by
    have : 2 ≤ D.R.f := by
      unfold Ranks.f Ranks.n
      have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos
      omega
    exact_mod_cast this
  have hr : (6 : ℝ) ≤ D.R.r := by
    have : 6 ≤ D.R.r := by
      unfold Ranks.r
      have := D.R.two_le_m
      have := D.R.m_add_three_le_k
      omega
    exact_mod_cast this
  have hA : 0 ≤ absA w := by unfold absA; positivity
  have hn' : (1 : ℝ) ≤ w.n := by exact_mod_cast hn
  have hs : absA w + (D.R.f : ℝ) * D.R.r * w.n + 1 ≤ w.size := by
    unfold WeightFamilies.Wt.size absA
    have hm : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    have h0 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n := by positivity
    have : (D.R.f : ℝ) * D.R.r * w.n ≤
        (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hm h0]
    linarith
  have hb : 0 ≤ Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    rw [Real.log_abs]
    exact Real.log_intCast_nonneg _
  unfold WeightAlgebra.Gc Zb
  exact gc_arith _ _ _ _ _ _ _ _ _ _ _ hf hr hL hA hn' hs (lamStar_nonneg_nat D)
    (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg _) hb (le_max_left _ _)

end GlobalTheory.RunIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupBoundsLeGeneratorConstantMulSizeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supBounds_le_generatorConstant_mul_size : ∀ (D : D7) (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j) (p : ℕ), 2 ≤ large₂.sc.L → 0 < w.n → (140 * D.R.r * large₂.sc.L * absA w + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L ≤ 400 * Zb D large₂ * w.size) ∧ (2 * (lamStar D + 2 * Real.log p) * w.size + 400 * Zb D large₂ * w.size + lamStar D * w.size ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) ∧ ((lamStar D + 2 * Real.log p) * w.size + (400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ B.KO) + Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO + 2) ≤ WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) p * w.size) := by
  first | exact @GlobalTheory.RunIn.sup_bounds_le_Gc | exact GlobalTheory.RunIn.sup_bounds_le_Gc | (intros; apply GlobalTheory.RunIn.sup_bounds_le_Gc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsValueBasisInSpanningForms
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsValueBasisInSpanningForms
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem exists_indep_of_span_image {α : Type} {δ : ℕ} (S : Set α) (v : α → Fin δ → ℂ)
    (h : Submodule.span ℂ (v '' S) = ⊤) :
    ∃ θ : Fin δ → α, (∀ i, θ i ∈ S) ∧ LinearIndependent ℂ fun i => v (θ i) := by
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent ℂ (v '' S)
  rw [h] at hsp
  let bs : Module.Basis b ℂ (Fin δ → ℂ) := Module.Basis.mk hli (by rw [Subtype.range_coe, hsp])
  let e : Fin δ ≃ b := (Pi.basisFun ℂ (Fin δ)).indexEquiv bs
  choose θ hθ hv using fun i : Fin δ => hb (e i).2
  refine ⟨θ, hθ, ?_⟩
  have : (fun i => v (θ i)) = (Subtype.val : b → Fin δ → ℂ) ∘ e := funext hv
  rw [this]
  exact hli.comp e e.injective

theorem ev_mem_sp_of_mem_span {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} (R : Rdg X)
    (u : WeightFamilies.Wt D j) (s : Set (B.Cusp j u)) (F : B.Cusp j u) (hF : F ∈ Submodule.span B.KO s) :
    R.ev (X.inc u F) ∈ R.sp u s := by
  induction hF using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul, R.ev_smul]; exact Submodule.smul_mem _ _ hx

theorem exists_valueBasis_in_spanning (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j)
    (ka wL wF : WeightFamilies.Wt D j) (N : ℕ) (w : Fin N → B.Cusp j wL) (R : Rdg X) (t : Idx D j N → ℂ) (T : ℕ)
    (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y) (hA : AnFacts R w t ka wF T Mg xs)
    (Sh : Set (B.Cusp j wF)) (hS : Submodule.span B.KO Sh = ⊤) :
    ∃ θ : Fin δ → B.Cusp j wF, (∀ i, θ i ∈ Sh) ∧
      LinearIndependent ℂ (vals xs fun i => R.ev (X.inc wF (θ i))) := by
  refine exists_indep_of_span_image Sh (fun F q => R.ev (X.inc wF F) (xs q)) ?_
  rw [eq_top_iff]
  intro v _
  obtain ⟨f, hf, hv⟩ := hA.interp v
  have h1 : R.sp wF Set.univ ≤ R.sp wF Sh := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨F, -, rfl⟩
    exact ev_mem_sp_of_mem_span R wF Sh F (hS ▸ Submodule.mem_top)
  have h2 : LinearMap.funLeft ℂ ℂ xs f ∈ (R.sp wF Sh).map (LinearMap.funLeft ℂ ℂ xs) :=
    Submodule.mem_map_of_mem (h1 hf)
  rw [Rdg.sp, Submodule.map_span, Set.image_image] at h2
  have h3 : v = LinearMap.funLeft ℂ ℂ xs f := funext fun q => (hv q).symm
  rw [h3]
  exact h2

end GlobalTheory.Shares
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsValueBasisInSpanningFormsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valueBasis_in_spanning_forms : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (N : ℕ) (w : Fin N → B.Cusp j wL) (R : Rdg X) (t : Idx D j N → ℂ) (T : ℕ) (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y), AnFacts R w t ka wF T Mg xs → ∀ Sh : Set (B.Cusp j wF), Submodule.span B.KO Sh = ⊤ → ∃ θ : Fin δ → B.Cusp j wF, (∀ i, θ i ∈ Sh) ∧ LinearIndependent ℂ (vals xs fun i => R.ev (X.inc wF (θ i))) := by
  first | exact @GlobalTheory.Shares.exists_valueBasis_in_spanning | exact GlobalTheory.Shares.exists_valueBasis_in_spanning | (intros; apply GlobalTheory.Shares.exists_valueBasis_in_spanning <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageTwoLeLAndSigns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem page_two_le_L_and_signs : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → 2 ≤ large₂.sc.L ∧ 2 ≤ D.R.f ∧ 6 ≤ D.R.r ∧ 0 ≤ lamStar D ∧ (1 ≤ j → 1 ≤ WeightFamilies.dimY D j) ∧ (FamilyHypotheses.SupBoundPageRows D large₂ ka ↔ ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka) := by
  intro D B P j X large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp hc
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hf : 2 ≤ D.R.f := by
    have : 0 < D.R.ord := D.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hr : 6 ≤ D.R.r := by unfold Ranks.r; omega
  refine ⟨?_, hf, hr, ?_, ?_, Iff.rfl⟩
  · obtain ⟨-, hS, -⟩ := hp
    have hn : ka.n = D.R.nV := hS.1
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hC, hZ, -⟩ := hS
    obtain ⟨-, -, -, -, hlf, -, -, -, hln⟩ := hc
    by_contra hL
    push_neg at hL
    have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast (by omega : 0 < D.R.f)
    have hr0 : (0 : ℝ) < D.R.r := by exact_mod_cast (by omega : 0 < D.R.r)
    have hrn : (D.R.r : ℝ) ≤ ka.n := by
      rw [hn]; exact_mod_cast (by unfold Ranks.nV; omega : D.R.r ≤ D.R.nV)
    have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
    have he4 : Real.exp 4 ≤ 81 := by
      have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc Real.exp 1 ^ 4 ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he 4
        _ = 81 := by norm_num
    have hf1 : (D.R.f : ℝ) ≤ 81 :=
      ((Real.log_le_iff_le_exp hf0).1 (by linarith : Real.log D.R.f ≤ 4)).trans he4
    have hr1 : (D.R.r : ℝ) ≤ 81 :=
      hrn.trans (((Real.log_le_iff_le_exp (hr0.trans_le hrn)).1
        (by linarith : Real.log ka.n ≤ 4)).trans he4)
    have hfr : (D.R.f : ℝ) * D.R.r ≤ 81 * 81 := mul_le_mul hf1 hr1 hr0.le (by norm_num)
    have hZ2 : Zb D large₂ ≤ 81 * 81 * 2 := by
      unfold Zb
      have := mul_pos hf0 hr0
      nlinarith
    have hC2 : (1000 : ℝ) ^ 20 ≤ H.C1 ^ 20 := pow_le_pow_left₀ (by norm_num) hC 20
    have : (81 * 81 * 2 : ℝ) < 1000 ^ 20 := by norm_num
    linarith
  · unfold lamStar
    have h1 := Real.log_natCast_nonneg (D.host.g 0 * D.host.g 1)
    have h2 := Real.log_natCast_nonneg (D.R.f ^ 2 * D.host.q * D.host.d)
    push_cast at h1 h2
    have e : 4 * ((D.R.f : ℝ) / 2) ^ 2 = (D.R.f : ℝ) ^ 2 := by ring
    rw [e]
    exact add_nonneg h1 h2
  · intro hj
    unfold WeightFamilies.dimY
    have hp5 : 5 ≤ (D.R.sigW j).1 := by
      show 5 ≤ D.R.k + j - 1
      omega
    have h1 : 1 ≤ (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) / 2 := by
      have : 5 * 4 ≤ (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) := Nat.mul_le_mul hp5 (by omega)
      omega
    exact Nat.mul_pos (by omega) (by omega)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankHost
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.ExtraWeight

theorem finrank_host (D : D7) : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  push_cast
  ring

theorem discr_rpow (D : D7) :
    |(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / D.R.f) = D.host.rdE ^ 2 := by
  have hf : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
  unfold Host.rdE
  rw [finrank_host, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  congr 1
  push_cast
  field_simp

theorem two_le_dimY (D : D7) {j : ℕ} (hj : j < D.R.m) (h1 : 1 ≤ j) : 2 ≤ WeightFamilies.dimY D j := by
  have hf : 8 ≤ D.R.f := D.eight_le_f
  have hk := D.R.m_add_three_le_k
  have hp : 1 ≤ (D.R.sigW j).1 := by unfold Ranks.sigW; simp only; omega
  have hq : 1 ≤ (D.R.sigW j).2 := by unfold Ranks.sigW; simp only; omega
  have hpq : 1 ≤ (D.R.sigW j).1 * (D.R.sigW j).2 := Nat.mul_pos hp hq
  unfold WeightFamilies.dimY
  calc 2 ≤ 8 * 1 := by norm_num
    _ ≤ _ := Nat.mul_le_mul hf (by omega)

theorem core (r f m ρ rd PP c T g DF q : ℝ) (hg : g = 1250 * r) (hr : 0 ≤ r) (hrT : r ≤ T) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ m) (hrd : 2 * f * m ≤ rd) (hPP : 0 < PP) (hq : 0 < q)
    (hc : c = rd ^ 7 * PP * DF ^ 2 / q) (hql : (rd ^ 7) ^ 4 * PP ^ 3 * DF ^ 2 ≤ q) (hgP : g * f * m ^ 3 ≤ PP ^ 2) :
    r * (1 + rd ^ 7 * T * c * (2 * f * ρ) ^ 2 * ρ / 2 / (1 / (2 * 5 ^ 4 * rd ^ 2))) ≤ 2 * T := by
  have h2f : 2 * f ≤ rd := by nlinarith
  have hrd1 : 1 ≤ rd := by linarith
  have hT : 0 ≤ T := hr.trans hrT
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hcP : c * (PP ^ 2 * rd ^ 21) ≤ 1 := by
    rw [hc, div_mul_eq_mul_div, div_le_one hq]
    calc _ = (rd ^ 7) ^ 4 * PP ^ 3 * DF ^ 2 := by ring
      _ ≤ q := hql
  have e : r * (1 + rd ^ 7 * T * c * (2 * f * ρ) ^ 2 * ρ / 2 / (1 / (2 * 5 ^ 4 * rd ^ 2))) =
      r + T * (c * ((g * f * ρ ^ 3) * (2 * f * rd ^ 9))) := by
    rw [hg]; field_simp; ring
  have a1 : g * f * ρ ^ 3 ≤ PP ^ 2 := by
    refine le_trans ?_ hgP
    have : 0 ≤ g * f := by rw [hg]; positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0 hρ 3) this
  have a2 : 2 * f * rd ^ 9 ≤ rd ^ 21 := by
    calc 2 * f * rd ^ 9 ≤ rd * rd ^ 9 := mul_le_mul_of_nonneg_right h2f (by positivity)
      _ = rd ^ 10 := by ring
      _ ≤ rd ^ 21 := pow_le_pow_right₀ hrd1 (by norm_num)
  have a3 : (g * f * ρ ^ 3) * (2 * f * rd ^ 9) ≤ PP ^ 2 * rd ^ 21 :=
    mul_le_mul a1 a2 (by positivity) (by positivity)
  have a4 : c * ((g * f * ρ ^ 3) * (2 * f * rd ^ 9)) ≤ 1 := (mul_le_mul_of_nonneg_left a3 hc0).trans hcP
  rw [e]
  have := mul_le_mul_of_nonneg_left a4 hT
  linarith

theorem numbers : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → j < D.R.m → 1 ≤ j → 1 ≤ WeightAlgebra.DF wL → 0 < WeightAlgebra.cc D large₂ C2 A2 CR wL ∧ (Tn : ℝ) * WeightAlgebra.cc D large₂ C2 A2 CR wL * g0 D ≤ 1 ∧ 1 ≤ WeightFamilies.RRv D K.CRm ∧ (D.R.r : ℝ) * (1 + WeightFamilies.c1 D K.CRm Tn (WeightAlgebra.cc D large₂ C2 A2 CR wL) j / (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / D.R.f)))) ≤ 2 * Tn ∧ addL wF wL Tn = ka ∧ 2 ≤ WeightFamilies.dimY D j ∧ 11 * WeightFamilies.dimY D j ^ 2 ≤ Tn := by
  intro D B P j X K Ch Ah Cq Aq large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hH ht hPg hj h1 hDF
  obtain ⟨hA, hS, h3, -, -⟩ := hH
  obtain ⟨hn, -, -, -, -, -, -, -, -, -, -, -, -, hnV, hL, hF, -, -, -, -, hrT, -, -, h11, -, hd⟩ := hS
  have hgP := g0fm3_le_of_dom hPg ht hd
  obtain ⟨e1, e2, e3⟩ := tie_eqs ht
  have hCR : CR = 7 := ht.2.2.2.2.2.1
  have hK : K.CRm = 7 := ht.2.2.2.2.2.2.1
  have hrd16 := sixteen_le_rdE_of_parA hA
  have hrd : 2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE := hA.2.2.2.2.2.2.2.2.2
  have hRR : WeightFamilies.RRv D 7 = D.host.rdE ^ 7 := by
    unfold WeightFamilies.RRv; exact_mod_cast Real.rpow_natCast D.host.rdE 7
  have hC : 1000 ≤ C2 := ht.1 ▸ hd.1
  have hPP : 0 < WeightFamilies.PPv D large₂ C2 A2 := by
    unfold WeightFamilies.PPv
    have := WeightFamilies.one_le_zBase large₂
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith) _)
  obtain ⟨hql, -, -, hTc, -, -⟩ := h3
  rw [Real.rpow_zero, one_mul, hCR, hRR] at hql
  rw [e1, e2, e3] at hTc
  have hDF' : (1 : ℝ) ≤ (WeightAlgebra.DF wL : ℝ) := by exact_mod_cast hDF
  have hrd0 : 0 < D.host.rdE := by linarith
  have hq : (0 : ℝ) < (qq D : ℝ) := lt_of_lt_of_le (by positivity) hql
  have hc : WeightAlgebra.cc D large₂ C2 A2 CR wL = D.host.rdE ^ 7 * WeightFamilies.PPv D large₂ C2 A2 * (WeightAlgebra.DF wL : ℝ) ^ 2 / (qq D : ℝ) := by
    unfold WeightAlgebra.cc; rw [hCR, hRR]
  refine ⟨by rw [hc]; positivity, hTc, ?_, ?_, ?_, two_le_dimY D hj h1, h11⟩
  · rw [hK, hRR]; exact one_le_pow₀ (by linarith)
  · rw [discr_rpow]
    unfold WeightFamilies.c1 WeightFamilies.dP
    rw [hK, hRR]
    push_cast
    have hf : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
    have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
    refine core _ _ (D.R.m : ℝ) _ _ _ _ _ (g0 D : ℝ) _ _ ?_ (Nat.cast_nonneg _) ?_ (by linarith) (by linarith)
      (Nat.cast_nonneg _) ?_ hrd hPP hq hc hql hgP
    · unfold g0; push_cast; norm_num
    · exact_mod_cast (by omega : D.R.r ≤ Tn)
    · have : WeightFamilies.rho D j ≤ D.R.m := by unfold WeightFamilies.rho Ranks.sigW; simp only; omega
      exact_mod_cast this
  · obtain ⟨f1, f2, f3⟩ := hF
    have l1 := hL.1
    obtain ⟨aP, aM, p1, p2, n, p3⟩ := ka
    unfold addL wadd wsmul
    simp only [WeightFamilies.Wt.mk.injEq]
    simp only at hn f2 f3
    refine ⟨?_, ?_, ?_⟩
    · funext τ i
      have := f2 τ i
      zify; linarith
    · funext τ i
      have := f3 τ i
      zify; linarith
    · rw [f1, l1, hn, hnV]

end GlobalTheory.ExtraWeight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRunParametersAtTypePrimesProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRunParametersAtTypePrimesProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunParametersAtRecord

theorem lower_real (R P d a r q : ℝ) (hR : 0 ≤ R) (hd : 1 ≤ d) (ha : 0 ≤ a) (hr : 0 ≤ r)
    (h1 : 90 * (a + 1) ≤ P) (h2 : r ≤ P) (hq : R ^ 4 * P ^ 3 * d ^ 2 ≤ q) :
    R ^ 4 * (90 * (a + d)) * d * r ≤ q := by
  have hP : 1 ≤ P := by linarith
  have e1 : 90 * (a + d) ≤ P * d := by nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : 0 ≤ d), mul_le_mul_of_nonneg_left hd ha]
  have e2 : r ≤ P ^ 2 := by nlinarith
  refine le_trans ?_ hq
  have hd0 : 0 ≤ d := by linarith
  have hP0 : 0 ≤ P := by linarith
  calc R ^ 4 * (90 * (a + d)) * d * r ≤ R ^ 4 * (P * d) * d * P ^ 2 := by gcongr
    _ = R ^ 4 * P ^ 3 * d ^ 2 := by ring

theorem run_at_record : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (S : Scal B) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → EtaleWeightGaps.PageSupp D large₂ B C2 A2 nW S wL → RunOK D.host.E D.R.r (WeightAlgebra.DF wL) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL))) D.R.m ∧ 8100 * Real.pi * wL.n * (D.R.m : ℝ) ^ 4 * (I2.dstar (E := D.host.E) D.R.m : ℝ) ^ 4 * I2.RR (E := D.host.E) / (D.host.g 0 * D.host.g 1 : ℕ) ≤ cc D large₂ C2 A2 CR wL ∧ p14 D.host.E D.R.r wL.n D.R.m ≤ (D.R.f * D.R.r * nW * Real.log ((D.host.g 0 : ℝ) * D.host.g 1) + nW * (Real.log 24 + D.R.f * D.R.m * Real.log (4 * D.R.f * D.R.m)) + (D.R.r + 2) * Real.log 2) / 2 ∧ D.R.f * D.R.r * (D.R.r + 1) ≤ 2 * wL.n := by
  intro D B P j X K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp ht hPg hSu
  obtain ⟨hA, hS, h3, -, -⟩ := hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcol, -, hL, -, -, -, -, -, -, h40, -, -, -, hd⟩ := hS
  obtain ⟨hq1, -, -, -, -, hq6⟩ := h3
  rw [Real.rpow_zero, one_mul] at hq1
  obtain ⟨h13, -, hf2, hr8, hDF⟩ := hSu
  have hn : wL.n = nW := hL.1
  have hC1 : H.C1 = C2 := ht.1
  rw [hC1] at hd
  have hCR : CR = 7 := ht.2.2.2.2.2.1
  have hA2 : 12 ≤ A2 := ht.2.2.2.2.2.2.2.1
  have hf := hostSize_f D
  have hrd := hostSize_rd D
  have h16 := EtaleWeightGaps.sixteen_le_rdE_of_parA hA
  have hm4 := EtaleWeightGaps.lift_index_pow_four_le_degree hPg
  have hf8 := D.eight_le_f
  have hm2 := D.R.two_le_m
  have hRR : WeightFamilies.RRv D CR = I2.RR (E := D.host.E) := by
    rw [hCR]
    unfold WeightFamilies.RRv I2.RR
    rw [hrd]
    exact_mod_cast Real.rpow_natCast D.host.rdE 7
  have hRR0 : 0 ≤ I2.RR (E := D.host.E) := by
    unfold I2.RR
    rw [hrd]
    positivity
  have hZ1 : 1 ≤ zBase large₂ := WeightFamilies.one_le_zBase large₂
  have h12 : WeightAlgebra.sizeConstantAtParamsWeight D nW ≤ WeightFamilies.PPv D large₂ C2 A2 := by
    refine le_trans hd.2.2.2.2.2.2.2.2.1 ?_
    unfold WeightFamilies.PPv
    refine mul_le_mul_of_nonneg_left ?_ (by linarith [hd.1])
    change zBase large₂ ^ 4 ≤ _
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by push_cast; linarith)
  have h90 : 90 * ((D.R.f : ℝ) * D.R.r + 1) ≤ WeightFamilies.PPv D large₂ C2 A2 := le_trans (le_max_left _ _) h12
  have hf8' : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
  have hr8' : (8 : ℝ) ≤ D.R.r := by exact_mod_cast hr8
  have hDF' : (3 : ℝ) ≤ (WeightAlgebra.DF wL : ℝ) := by exact_mod_cast hDF
  have hrP : (D.R.r : ℝ) ≤ WeightFamilies.PPv D large₂ C2 A2 := by nlinarith
  have hq2 : (2 : ℝ) ≤ (qq D : ℝ) := by
    have : (0 : ℝ) ≤ ((WeightFamilies.dimY D j + 4) * WeightAlgebra.DF wL : ℝ) := by positivity
    linarith
  have hq2' : 2 ≤ qq D := by exact_mod_cast hq2
  have hg0 : 2 ≤ D.host.g 0 := le_trans hq2' (min_le_left _ _)
  have hg1 : 2 ≤ D.host.g 1 := le_trans hq2' (min_le_right _ _)
  have hqg : qq D ≤ D.host.g 0 * D.host.g 1 :=
    le_trans (min_le_left _ _) (Nat.le_mul_of_pos_right _ (by omega))
  have hqg' : (qq D : ℝ) ≤ ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by exact_mod_cast hqg
  have hds : (I2.dstar (E := D.host.E) D.R.m : ℝ) = 2 * (D.R.f : ℝ) * (D.R.m : ℝ) := by
    unfold I2.dstar
    rw [hf]
    push_cast
    ring
  refine ⟨?_, ?_, ?_, by omega⟩
  · have key := GlobalTheory.RunParametersOfLower.runOK_of_le D.host.E D.R.r (WeightAlgebra.DF wL) (D.host.g 0 * D.host.g 1) D.R.m (by omega)
      (by rw [hf]; nlinarith) (by omega) (by rw [hf]; exact_mod_cast hm4) (by rw [hf, hrd]; exact hf2)
      (by rw [hrd]; exact h16)
      (by
        rw [hf]
        rw [hRR] at hq1
        exact lower_real _ _ _ _ _ _ hRR0 (by linarith) (by positivity) (by positivity) h90 hrP (hq1.trans hqg'))
    rw [hf] at key
    exact key
  · unfold cc
    rw [hRR, hds, hn]
    have a1 : 16200 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤
        WeightFamilies.PPv D large₂ C2 A2 := le_trans (le_max_left _ _) h13
    have a0 : 0 ≤ 8100 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 := by positivity
    have a2 : 8100 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤
        WeightFamilies.PPv D large₂ C2 A2 := by linarith
    have hP0 : 0 ≤ WeightFamilies.PPv D large₂ C2 A2 := le_trans a0 a2
    have a3 : WeightFamilies.PPv D large₂ C2 A2 ≤ WeightFamilies.PPv D large₂ C2 A2 * (WeightAlgebra.DF wL : ℝ) ^ 2 :=
      le_mul_of_one_le_right hP0 (one_le_pow₀ (by linarith))
    refine div_le_div₀ (by positivity) ?_ (by linarith) hqg'
    rw [mul_comm _ (I2.RR (E := D.host.E)), mul_assoc (I2.RR (E := D.host.E))]
    exact mul_le_mul_of_nonneg_left (a2.trans a3) hRR0
  · unfold p14
    rw [hds, hn]
    have g0' : (2 : ℝ) ≤ D.host.g 0 := by exact_mod_cast hg0
    have g1' : (2 : ℝ) ≤ D.host.g 1 := by exact_mod_cast hg1
    have g4 : (4 : ℝ) ≤ (D.host.g 0 : ℝ) * D.host.g 1 := by nlinarith
    have b1 : Real.log Real.pi ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_le_four])
    have b0 : 0 ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := Real.log_nonneg (by linarith)
    have hW : (1 : ℝ) ≤ nW := by exact_mod_cast (by omega : 1 ≤ nW)
    have b2 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * nW :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) hW
    have b3 := le_mul_of_one_le_left b0 b2
    have e1 : 2 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) = 4 * D.R.f * D.R.m := by ring
    have e2 : 2 * (D.R.f : ℝ) * (D.R.m : ℝ) / 2 = D.R.f * D.R.m := by ring
    rw [e1, e2]
    linarith

end GlobalTheory.RunParametersAtRecord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRunParametersAtTypePrimesProductStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRunParameters_at_typePrimes_product : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (S : Scal B) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → EtaleWeightGaps.PageSupp D large₂ B C2 A2 nW S wL → RunOK D.host.E D.R.r (WeightAlgebra.DF wL) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL))) D.R.m ∧ 8100 * Real.pi * wL.n * (D.R.m : ℝ) ^ 4 * (I2.dstar (E := D.host.E) D.R.m : ℝ) ^ 4 * I2.RR (E := D.host.E) / (D.host.g 0 * D.host.g 1 : ℕ) ≤ cc D large₂ C2 A2 CR wL ∧ p14 D.host.E D.R.r wL.n D.R.m ≤ (D.R.f * D.R.r * nW * Real.log ((D.host.g 0 : ℝ) * D.host.g 1) + nW * (Real.log 24 + D.R.f * D.R.m * Real.log (4 * D.R.f * D.R.m)) + (D.R.r + 2) * Real.log 2) / 2 ∧ D.R.f * D.R.r * (D.R.r + 1) ≤ 2 * wL.n := by
  first | exact @GlobalTheory.RunParametersAtRecord.run_at_record | exact GlobalTheory.RunParametersAtRecord.run_at_record | (intros; apply GlobalTheory.RunParametersAtRecord.run_at_record <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueLinearInPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueLinearInPolynomial
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

namespace GlobalTheory.ShortValueLinear

theorem isHomogeneous_of_rowDeg {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
    {a : T → ℕ → ℕ} {P : MvPolynomial (Letter T r n) k} (hP : RowDeg r n k a P) :
    P.IsHomogeneous (∑ σ : T, ∑ i : Fin (r σ), a σ i) := by
  classical
  intro m hm
  have hmS : m ∈ P.support := MvPolynomial.mem_support_iff.mpr hm
  have key : ∀ (σ : T) (i : Fin (r σ)), a σ (i : ℕ) = ∑ b, m ⟨σ, (i, b)⟩ :=
    fun σ i => (hP m hmS σ i).symm
  simp only [key]
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun σ _ => Fintype.sum_prod_type _

theorem sum_support_eq_constr {ι F S : Type} [Field F] [CommRing S] [Algebra F S]
    (G : (ι →₀ ℕ) → S) (P : MvPolynomial ι F) :
    ∑ m ∈ P.support, algebraMap F S (P.coeff m) * G m =
      (MvPolynomial.basisMonomials ι F).constr F G P := by
  classical
  rw [Module.Basis.constr_apply, Finsupp.sum]
  refine Finset.sum_congr ?_ fun μ _ => ?_
  · ext μ
    simp [MvPolynomial.basisMonomials]
  · simp [MvPolynomial.basisMonomials, Algebra.smul_def]

theorem formula_linear {ι F S Qt J : Type} [Field F] [CommRing S] [Algebra F S] [Finite Qt] [Fintype J]
    (k N : F) (w : Qt → F) (G : Qt → J → (ι →₀ ℕ) → S) (d m : ℕ) (cf : Fin m → F)
    (Q : Fin m → MvPolynomial ι F) (hQ : ∀ i, (Q i).IsHomogeneous d) :
    algebraMap F S (k * (N ^ (∑ i, cf i • Q i).totalDegree)⁻¹) *
        ∑ᶠ q, algebraMap F S (w q) * ∑ j, ∑ μ ∈ (∑ i, cf i • Q i).support,
          algebraMap F S ((∑ i, cf i • Q i).coeff μ) * G q j μ =
      ∑ i, algebraMap F S (cf i) * (algebraMap F S (k * (N ^ (Q i).totalDegree)⁻¹) *
        ∑ᶠ q, algebraMap F S (w q) * ∑ j, ∑ μ ∈ (Q i).support,
          algebraMap F S ((Q i).coeff μ) * G q j μ) := by
  classical
  have := Fintype.ofFinite Qt
  set B := MvPolynomial.basisMonomials ι F
  have hsum : ∀ (P : MvPolynomial ι F) (q : Qt) (j : J),
      ∑ μ ∈ P.support, algebraMap F S (P.coeff μ) * G q j μ = B.constr F (G q j) P :=
    fun P q j => sum_support_eq_constr (G q j) P
  simp only [hsum, finsum_eq_sum_of_fintype]
  have hpre : ∀ P : MvPolynomial ι F, P.IsHomogeneous d →
      algebraMap F S (k * (N ^ P.totalDegree)⁻¹) *
          ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) P =
        algebraMap F S (k * (N ^ d)⁻¹) * ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) P := by
    intro P hP
    by_cases hP0 : P = 0
    · simp [hP0]
    · rw [hP.totalDegree hP0]
  have hQs : (∑ i, cf i • Q i).IsHomogeneous d := by
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hQ i))
  have hR : ∀ i, algebraMap F S (cf i) * (algebraMap F S (k * (N ^ (Q i).totalDegree)⁻¹) *
        ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) (Q i)) =
      algebraMap F S (cf i) * (algebraMap F S (k * (N ^ d)⁻¹) *
        ∑ q, algebraMap F S (w q) * ∑ j, B.constr F (G q j) (Q i)) :=
    fun i => by rw [hpre _ (hQ i)]
  have hlin : ∀ (q : Qt) (j : J), B.constr F (G q j) (∑ i, cf i • Q i) =
      ∑ i, algebraMap F S (cf i) * B.constr F (G q j) (Q i) := by
    intro q j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.smul_def]
  rw [hpre _ hQs]
  simp only [hR]
  simp only [hlin, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.ShortValueLinear

namespace GlobalTheory

theorem shortThetaValue_linear : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (w : (Fin n → LevQ Dw l) → c.F) (β : c.F) (m : ℕ) (cf : Fin m → c.F) (Q : Fin m → MvPolynomial (LtN Dw n) c.F), (∀ i, Q i ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) (u : Fin m → S), ShortValAt Xo c nab w Λ β N (∑ i, cf i • Q i) y v → (∀ i, ShortValAt Xo c nab w Λ β N (Q i) y (u i)) → v = ∑ i, algebraMap c.F S (cf i) * u i := by
  intro hC E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hT hL a w β m cf Q hQ S _ _ y v u hv hu
  classical
  have : Finite (LevQ Dw l) := GlobalTheory.ShortValue.finite_levelQuotient Dw l
  have hEU := fun i => GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw l
    Xo c nab hnab n Λ N hU hT hL a (Q i) (hQ i) w β
  have hRow : ∀ i, RowDeg Dw.mult n c.F (fun τ j => a (τ, j)) (Q i) := by
    intro i
    have h := hQ i
    unfold HHa at h
    simp only [Set.mem_setOf_eq] at h
    exact h.2.2
  have hQd := fun i => GlobalTheory.ShortValueLinear.isHomogeneous_of_rowDeg (hRow i)
  unfold ShortValAt at hv
  obtain ⟨S', _i1, _i2, φ, y', z, tp, F, hff, hfr, hz, hgeo, htp, huu, hφv⟩ := hv
  have hnat : ∀ i, φ (u i) = algebraMap c.F S' (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((N : c.F) ^ (Q i).totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F S' (w q) *
        ∑ j, ∑ μ ∈ (Q i).support, algebraMap c.F S' ((Q i).coeff μ) *
          ∏ b, nab y' ((N : ℤ) ^ 2) (F q j b) (colOf μ b) := by
    intro i
    refine (hEU i).2 S S' φ y y' hfr (u i) _ (hu i) ?_
    unfold ShortValAt
    exact ⟨S', _i1, _i2, AlgHom.id c.F S', y', z, tp, F,
      RingHom.FaithfullyFlat.of_bijective ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩,
      GlobalTheory.Frames.frMapUniq_refl y', hz, hgeo, htp, huu, rfl⟩
  have hlin := GlobalTheory.ShortValueLinear.formula_linear (S := S')
    (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹) (N : c.F) w
    (fun q j μ => ∏ b, nab y' ((N : ℤ) ^ 2) (F q j b) (colOf μ b)) _ m cf Q hQd
  apply RingHom.FaithfullyFlat.injective hff
  change φ v = φ (∑ i, algebraMap c.F S (cf i) * u i)
  rw [hφv]
  refine hlin.trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul φ, AlgHom.commutes, hnat i]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueLinearInPolynomialStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_theta_value_linear_in_polynomial : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (w : (Fin n → LevQ Dw l) → c.F) (β : c.F) (m : ℕ) (cf : Fin m → c.F) (Q : Fin m → MvPolynomial (LtN Dw n) c.F), (∀ i, Q i ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) (u : Fin m → S), ShortValAt Xo c nab w Λ β N (∑ i, cf i • Q i) y v → (∀ i, ShortValAt Xo c nab w Λ β N (Q i) y (u i)) → v = ∑ i, algebraMap c.F S (cf i) * u i := by
  first | exact @GlobalTheory.shortThetaValue_linear | exact GlobalTheory.shortThetaValue_linear | (intros; apply GlobalTheory.shortThetaValue_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogLeOfLePowMulPow
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem log_le_of_le_pow_mul_pow {N g₀ g₁ d X m : ℕ} {a c P : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hP : 0 ≤ P)
    (h₀ : Real.log g₀ ≤ a) (h₁ : Real.log g₁ ≤ a) (hd : Real.log d ≤ P) (hX : Real.log X ≤ c)
    (hN : N ≤ (g₀ * g₁) ^ m * (d * X ^ m)) : Real.log N ≤ m * (2 * a + c) + P := by
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · simp only [Nat.cast_zero, Real.log_zero]; positivity
  have key : ∀ (x : ℕ) (t : ℝ), Real.log x ≤ t → (x : ℝ) ≤ Real.exp t := fun x t h =>
    (Real.le_exp_log _).trans (Real.exp_le_exp.2 h)
  have e₀ := key _ _ h₀
  have e₁ := key _ _ h₁
  have e₂ := key _ _ hd
  have e₃ := key _ _ hX
  have hN' : (N : ℝ) ≤ ((g₀ : ℝ) * g₁) ^ m * (d * (X : ℝ) ^ m) := by exact_mod_cast hN
  rw [Real.log_le_iff_le_exp (by exact_mod_cast hpos)]
  calc (N : ℝ) ≤ ((g₀ : ℝ) * g₁) ^ m * (d * (X : ℝ) ^ m) := hN'
    _ ≤ (Real.exp a * Real.exp a) ^ m * (Real.exp P * Real.exp c ^ m) := by gcongr
    _ = Real.exp (m * (2 * a + c) + P) := by
      rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring

theorem frn_le_size_sub_one {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) :
    ((D.R.f * D.R.r * w.n : ℕ) : ℝ) ≤ w.size - 1 := by
  unfold WeightFamilies.Wt.size
  have h1 : (0 : ℝ) ≤ ∑ τ, (∑ i, (w.aP τ i : ℝ) + ∑ i, (w.aM τ i : ℝ)) := by positivity
  have h2 : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  have h3 : (D.R.f : ℝ) * 1 * D.R.r * w.n ≤ D.R.f * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * D.R.r * w.n := by
    gcongr
  rw [Nat.cast_mul, Nat.cast_mul]
  linarith

theorem log_count_le_mul_size : ∀ (D : D7) (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j) (N : ℕ) (Prw : ℝ), 2 ≤ large₂.sc.L → 0 < w.n → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → OPO large₂ B → 38 * large₂.sc.L + PO D large₂ ≤ Prw → N ≤ (D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ B.KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n)) → Real.log N ≤ Prw * (w.size - 1) := by
  intro D B large₂ j w N Prw hL hn hp hO hPrw hN
  have hP : 0 ≤ PO D large₂ := by
    unfold PO
    have : 0 ≤ large₂.sc.L := by linarith
    positivity
  have hX : Real.log ((1 + WeightAlgebra.DF w : ℕ) : ℝ) ≤ 2 * large₂.sc.L := by
    rw [Nat.cast_add, Nat.cast_one]; exact hp.2.2.2.2.2.2.2.1
  have h := log_le_of_le_pow_mul_pow (by linarith) (by linarith) hP (hp.1 0) (hp.1 1) hO.1 hX hN
  have hs := frn_le_size_sub_one w
  have hf : 0 < D.R.f := by
    have := D.R.two_le_m
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hm : (1 : ℝ) ≤ ((D.R.f * D.R.r * w.n : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hf hr) hn
  generalize ((D.R.f * D.R.r * w.n : ℕ) : ℝ) = m at h hs hm
  generalize w.size - 1 = s at hs ⊢
  have hs0 : 0 ≤ s := by linarith
  calc Real.log N ≤ m * (2 * (9 * large₂.sc.L + 1) + 2 * large₂.sc.L) + PO D large₂ := h
    _ ≤ s * (38 * large₂.sc.L) + PO D large₂ * s := by
      have a1 : m * (2 * (9 * large₂.sc.L + 1) + 2 * large₂.sc.L) ≤ s * (38 * large₂.sc.L) :=
        mul_le_mul hs (by linarith) (by linarith) hs0
      have a2 : PO D large₂ ≤ PO D large₂ * s := le_mul_of_one_le_right hP (hm.trans hs)
      linarith
    _ = (38 * large₂.sc.L + PO D large₂) * s := by ring
    _ ≤ Prw * s := mul_le_mul_of_nonneg_right hPrw hs0

end GlobalTheory.RunIn
end
