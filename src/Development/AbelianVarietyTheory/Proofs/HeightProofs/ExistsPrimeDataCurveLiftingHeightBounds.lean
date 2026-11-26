module

public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.TranscendenceDegreeRatiosCuspFormsComponents
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.TorusAtExists
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeightInequalitiesIndefiniteLiftIndex
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeightInequalityDefiniteLiftIndex
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRealisationPrimeDataCurveLiftingStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PageHypothesesAtCusp
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SetConstantsGoodEmbeddingRecursion
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SetConstantsGoodEmbeddingRecursion
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

noncomputable section

namespace GlobalTheory.BigRec

section Inst

variable {D : D7} {T : Top D}

variable (h : LawsP T) {j : ℕ} (hj : InR D j)

end Inst


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem bigAt_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (c : ℝ) (large₂ : SizeData₂ D) (CK C1 A1 h0 : ℝ) (Tn nP nW : ℕ), SetC large₂ (recPlus h j hj) CK C1 A1 ka wL wF Tn nP nW h0 → NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G.w i).1) → (j < D.R.m → 0 < G.iet ∧ (recPlus h j hj).NonZeroComp _ G.et ∧ ∃ σ, GoodEmb T.Q.c σ ∧ PhRec h j σ G.w G.iet G.et c) → 0 ≤ c → 2 * c * g0 D ≤ 1 → (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW ∧ ∃ th : (recB h.toLawsCore).Cusp j w1, (recPlus h j hj).NonZeroComp w1 th) → BigAt h j hj hG G := by
  intro D T h j hj hG ka wL wF G c large₂ CK C1 A1 h0 Tn nP nW hS hN hE hc hcg _
  exact ⟨hN, GlobalTheory.T.transcendenceDegree_ratios_cuspForms_components D T h j hj hG ka wL wF G c large₂ CK C1 A1 h0 Tn nP nW hS hN hE hc hcg⟩

end GlobalTheory.BigRec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SetConstantsGoodEmbeddingRecursionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.set_constants_good_embedding_recursion : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (c : ℝ) (large₂ : SizeData₂ D) (CK C1 A1 h0 : ℝ) (Tn nP nW : ℕ), SetC large₂ (recPlus h j hj) CK C1 A1 ka wL wF Tn nP nW h0 → NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G.w i).1) → (j < D.R.m → 0 < G.iet ∧ (recPlus h j hj).NonZeroComp _ G.et ∧ ∃ σ, GoodEmb T.Q.c σ ∧ PhRec h j σ G.w G.iet G.et c) → 0 ≤ c → 2 * c * g0 D ≤ 1 → (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW ∧ ∃ th : (recB h.toLawsCore).Cusp j w1, (recPlus h j hj).NonZeroComp w1 th) → BigAt h j hj hG G := by
  first | exact @GlobalTheory.BigRec.bigAt_record | exact GlobalTheory.BigRec.bigAt_record | (intros; apply GlobalTheory.BigRec.bigAt_record <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PageHypothesesAtCusp
noncomputable section

namespace GlobalTheory.RunJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lieFac_scalar {D : D7} (T : Top D) (j i : ℕ) : lieFac (T.Q.Dw j) (xiR D) (wtA (wEt D j i)) = 1 := by
  have : ∀ x, wtA (wEt D j i) x = 0 := by
    intro x
    simp [wtA, wEt, WeightAlgebra.wscalar, ext0]
  simp [lieFac, this]

theorem weight_add_eq_smul_of_G2 {D : D7} {j : ℕ} {wL wF w2 : WeightFamilies.Wt D j} (h : IsG2 wL wF w2) :
    wadd wF w2 = wsmul (WeightFamilies.dimY D j + 4) wL := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold wadd wsmul
  congr 1
  · funext τ i; rw [add_comm]; exact h2 τ i
  · funext τ i; rw [add_comm]; exact h3 τ i
  · rw [add_comm]; exact h1

theorem thR_pos {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (hg : ∀ i, 0 < D.host.g i) (hd : 0 < DF w) : 0 < thR w := by
  have hf : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.f D.host.E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.f
    have h1 := IsTotallyComplex.finrank D.host.E
    have h2 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    omega
  have hrd : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.rd D.host.E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.rd
    exact Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero D.host.E))) _
  have h0 := hg 0
  have h1 := hg 1
  unfold thR I2.th I2.RR
  positivity


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem curveHyp_of_run : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (hG : GenFrEx (T.Q.Xo j) T.Q.c), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → ∃ g0 : (recB h.toLawsCore).Cusp j wF, CurveHyp h j hj hG ka wL wF (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) S g0 := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus hG hP hC G hGen hEta
  obtain ⟨⟨g0, hg0, -⟩, hnz⟩ := GlobalTheory.T.exists_cuspForm_nonzero_everyComponent D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hG hP
  obtain ⟨hT, hN, hlN, hZ, hLow⟩ := hGen
  have hZb : 0 ≤ Zb D large₂ := by
    have hs := hP.hyp.2.1
    have hd : DomAt D large₂ j nW H.C1 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    exact le_trans (by positivity) hd.2.1
  have hC2 : 0 ≤ C2 := by
    have hs := hP.hyp.2.1
    have hd : DomAt D large₂ j nW H.C1 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have := hd.1
    rw [hP.tie.1] at this
    linarith
  have hrow := (GlobalTheory.T.lowerBoundConst_at_large_multiple_numerical_bounds D _ _ j (recPJ h j hj) large₂ H C2 A2 CT ka wL wF Tn nP nW h0 1 G.N 1 hj hP one_pos hN one_pos hlN
    (by rw [Nat.cast_one, Real.log_one]; positivity)).2.2.2.2.2.2.2.2.1
  have hc0 : 0 ≤ cc D large₂ C2 A2 7 wL := by
    have h1 : 0 ≤ zBase large₂ := hZb
    have h2 : 0 ≤ D.host.rdE := le_trans (by positivity) hP.frd
    unfold cc WeightFamilies.RRv WeightFamilies.PPv
    positivity
  obtain ⟨hsz, PL, lN, -, -, hI1, w2, hw2, th2, -, hth2, -⟩ :=
    (FamilyHypotheses.fourthHypothesis_iff_sizes_and_index large₂ (recPJ h j hj) H C2 A2 7 ka wL wF Tn nW).1 hC.2.2.2.2.2.2.1
  have hth : 0 < thR wL := thR_pos wL (fun i => lt_of_le_of_lt (Nat.zero_le _) (hsz.2.2.2.2.2 i))
    (lt_of_lt_of_le (by norm_num) hP.df)
  refine ⟨g0, hT.1, ?_, ⟨WeightFamilies.dimY D j + 4, w2, th2, weight_add_eq_smul_of_G2 hw2, (hnz w2 th2 hth2).1⟩, hg0⟩
  refine GlobalTheory.T.set_constants_good_embedding_recursion D T h j hj hG ka wL wF (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj))
    (cc D large₂ C2 A2 7 wL) large₂ H.CK H.C1 H.A1 h0 Tn nP nW hP.hyp.2.1 hZ (fun hjm => ?_) hc0 (by linarith) (fun hjm => ?_)
  · obtain ⟨hi, hcu, -, -, hA, -⟩ := hEta hjm
    refine ⟨hi, hcu.2, T.σ₀, T.toCore.good_σ₀, ?_⟩
    have e : Fin (G.N - 1 + 1) ≃ Fin G.N := finCongr (by omega)
    refine GlobalTheory.BigRec.phRec_of_firstMin D T h j hj T.σ₀ wL G.N (G.N - 1) G.iet G.w e G.et (thR wL) (p14R wL) (DF wL)
      (200000 * zBase large₂ ^ 2) _ T.toCore.good_σ₀ hth (fun σ hσ k x hx => ?_) hZ (fun k x hx => ?_)
    · have h1 := hLow σ hσ k x hx
      rw [← e.sum_comp] at h1
      exact h1
    · have h1 := hA T.σ₀ T.toCore.good_σ₀ k x hx
      rw [lieFac_scalar, one_mul] at h1
      exact h1
  · obtain ⟨w1, hw1, th1, -, hth1, -⟩ := hI1 hjm
    exact ⟨w1, hw1, th1, hth1⟩

end GlobalTheory.RunJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PageHypothesesAtCuspStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.page_hypotheses_at_cusp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (hG : GenFrEx (T.Q.Xo j) T.Q.c), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → ∃ g0 : (recB h.toLawsCore).Cusp j wF, CurveHyp h j hj hG ka wL wF (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) S g0 := by
  first | exact @GlobalTheory.RunJoin.curveHyp_of_run | exact GlobalTheory.RunJoin.curveHyp_of_run | (intros; apply GlobalTheory.RunJoin.curveHyp_of_run <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PhiFDEqZeroAtLastIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumSqGeAndPhiEqZeroDefinite
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumSqGeAndPhiEqZeroDefinite
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate nonZeroDivisors

namespace GlobalTheory.DefiniteMin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_mulVec_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    FD.hermC τ G (P.mulVec w) (P.mulVec w) = ∑ a, ∑ b, w a * FD.gram τ G P a b * conj (w b) := by
  have h1 : FD.hermC τ G (P.mulVec w) (P.mulVec w) =
      ∑ a, ∑ b, ∑ c, ∑ d, w c * (P a c * τ (G a b) * conj (P b d)) * conj (w d) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [FD.hermC, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have h2 : ∑ a, ∑ b, w a * FD.gram τ G P a b * conj (w b) =
      ∑ c, ∑ d, ∑ a, ∑ b, w c * (P a c * τ (G a b) * conj (P b d)) * conj (w d) := by
    simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  rw [h1, h2]
  calc _ = ∑ a, ∑ c, ∑ b, ∑ d, w c * (P a c * τ (G a b) * conj (P b d)) * conj (w d) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, w c * (P a c * τ (G a b) * conj (P b d)) * conj (w d) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, w c * (P a c * τ (G a b) * conj (P b d)) * conj (w d) :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem hermC_neg (X : FD.Data E r) (h0 : X.p0 = 0) (τ : X.Ψ) {v : Fin r → ℂ} (hv : v ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ FD.hermC τ.1 X.Gm v v = -(s : ℂ) := by
  obtain ⟨P, hP, hG⟩ := X.signature τ
  set w := P⁻¹.mulVec v with hw
  have hPw : P.mulVec w = v := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hP), Matrix.one_mulVec]
  have hw0 : w ≠ 0 := by
    intro h
    apply hv
    rw [← hPw, h, Matrix.mulVec_zero]
  refine ⟨∑ a, Complex.normSq (w a), ?_, ?_⟩
  · obtain ⟨a, ha⟩ := Function.ne_iff.mp hw0
    exact lt_of_lt_of_le (Complex.normSq_pos.mpr ha)
      (Finset.single_le_sum (fun i _ => Complex.normSq_nonneg (w i)) (Finset.mem_univ a))
  · rw [← hPw, hermC_mulVec_mulVec, hG]
    simp only [Matrix.diagonal_apply, FD.sgn, h0, Nat.not_lt_zero, if_false]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Complex.mul_conj]
    ring

theorem map_herm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → E) :
    τ (FD.herm G u v) = FD.hermC τ G (FD.Data.emb τ u) (FD.Data.emb τ v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [FD.herm, FD.hermC, FD.Data.emb, FD.cc, map_sum, map_mul,
    NumberField.IsCMField.complexEmbedding_complexConj]

theorem posPart_eq_zero (X : FD.Data E r) (h0 : X.p0 = 0) (x : FD.Frame X.Ψ r) (τ : X.Ψ)
    (v : Fin r → ℂ) : X.posPart x τ v = 0 := by
  have : IsEmpty (Fin X.p0) := by rw [h0]; infer_instance
  simp [FD.Data.posPart]

theorem sum_norm_eq_two_mul (X : FD.Data E r) (y : E) :
    ∑ σ : E →+* ℂ, ‖σ y‖ = ∑ τ : X.Ψ, 2 * ‖τ.1 y‖ := by
  classical
  rw [← Finset.sum_add_sum_compl X.Ψ (fun σ => ‖σ y‖)]
  have hc : ∑ σ ∈ X.Ψᶜ, ‖σ y‖ = ∑ σ ∈ X.Ψ, ‖σ y‖ := by
    refine Finset.sum_nbij' (fun σ => ComplexEmbedding.conjugate σ)
      (fun σ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_compl] at hσ ⊢
      rw [X.cmType, ComplexEmbedding.involutive_conjugate E σ]
      exact hσ
    · intro σ hσ
      simp only [Finset.mem_compl] at hσ ⊢
      exact (X.cmType σ).mp hσ
    · intro σ _
      exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _
      exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
  rw [hc, ← two_mul, Finset.mul_sum, ← Finset.sum_coe_sort X.Ψ]

private theorem one_le_abs_norm_mul_abs_discr_of_trace_int {β : E}
    (hβ : ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (β * a) = k) (h0 : β ≠ 0) :
    (1 : ℚ) ≤ |Algebra.norm ℚ β| * |(NumberField.discr E : ℚ)| := by
  classical
  set D : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.dual ℤ ℚ 1 with hDdef
  have h1ne : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hD : D ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ h1ne
  have hmem : β ∈ D := by
    rw [hDdef, FractionalIdeal.mem_dual h1ne]
    intro a ha
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 E)⁰).mp ha
    obtain ⟨k, hk⟩ := hβ a'
    exact ⟨k, by rw [Algebra.traceForm_apply]; exact hk.symm⟩
  have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ β * D⁻¹ ≤ 1 := by
    calc _ ≤ D * D⁻¹ := mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.mpr hmem) _
      _ = 1 := mul_inv_cancel₀ hD
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    rw [FractionalIdeal.coeIdeal_bot, eq_comm, mul_eq_zero,
      FractionalIdeal.spanSingleton_eq_zero_iff, inv_eq_zero] at hI
    rcases hI with h | h
    · exact h0 h
    · exact hD h
  have hdiff : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = D⁻¹ :=
    coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E)
  have key := congrArg FractionalIdeal.absNorm hI
  rw [FractionalIdeal.coeIdeal_absNorm, map_mul, FractionalIdeal.absNorm_span_singleton, ← hdiff,
    FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal E (𝓞 E)] at key
  have h1 : (1 : ℚ) ≤ Ideal.absNorm I := by
    have : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  rw [key] at h1
  simpa [Nat.cast_natAbs] using h1

theorem finrank_div_rd_le {β : E} (hβ : ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (β * a) = k)
    (h0 : β ≠ 0) : (Module.finrank ℚ E : ℝ) / I2.PT.rd E ≤ ∑ σ : E →+* ℂ, ‖σ β‖ := by
  classical
  have hNq := one_le_abs_norm_mul_abs_discr_of_trace_int hβ h0
  have hN : (1 : ℝ) ≤ |(Algebra.norm ℚ β : ℝ)| * |(NumberField.discr E : ℝ)| := by
    have := (Rat.cast_le (K := ℝ)).mpr hNq
    simpa using this
  set n := Module.finrank ℚ E with hn_def
  have hn : 0 < n := Module.finrank_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : Fintype.card (E →+* ℂ) = n := NumberField.Embeddings.card E ℂ
  have hprod : ∏ σ : E →+* ℂ, ‖σ β‖ = |(Algebra.norm ℚ β : ℝ)| := by
    have h := congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ β)
    rw [norm_prod, ← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => ‖f β‖)
      (fun φ => ‖φ β‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
    rw [← h, eq_ratCast, Complex.norm_ratCast]
  have hgm : (∏ σ : E →+* ℂ, ‖σ β‖) ^ ((n : ℝ)⁻¹) ≤ (∑ σ : E →+* ℂ, ‖σ β‖) / n := by
    have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : E →+* ℂ => (1 : ℝ))
      (fun σ => ‖σ β‖) (fun _ _ => zero_le_one) (by simp [hcard, hn]) (fun _ _ => norm_nonneg _)
    simpa [hcard] using h
  rw [hprod] at hgm
  have hd : 0 < |(NumberField.discr E : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast NumberField.discr_ne_zero E
  have hdN : |(NumberField.discr E : ℝ)|⁻¹ ≤ |(Algebra.norm ℚ β : ℝ)| := by
    rw [inv_eq_one_div, div_le_iff₀ hd]
    exact hN
  have hlow : (I2.PT.rd E)⁻¹ ≤ |(Algebra.norm ℚ β : ℝ)| ^ ((n : ℝ)⁻¹) := by
    have hrd : I2.PT.rd E = |(NumberField.discr E : ℝ)| ^ (1 / (n : ℝ)) := rfl
    rw [hrd, ← Real.inv_rpow (abs_nonneg _), one_div]
    exact Real.rpow_le_rpow (inv_nonneg.mpr (abs_nonneg _)) hdN (inv_nonneg.mpr hnR.le)
  calc (n : ℝ) / I2.PT.rd E = n * (I2.PT.rd E)⁻¹ := div_eq_mul_inv _ _
    _ ≤ n * ((∑ σ : E →+* ℂ, ‖σ β‖) / n) :=
        mul_le_mul_of_nonneg_left (hlow.trans hgm) hnR.le
    _ = ∑ σ : E →+* ℂ, ‖σ β‖ := by field_simp

theorem two_f_div_rd_le_la1sq (X : FD.Data E r) (hr : 0 < r) (h0 : X.p0 = 0)
    (hint : ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * FD.herm X.Gm u v) = k)
    (x : FD.Frame X.Ψ r) : 2 * (I2.PT.f E : ℝ) / I2.PT.rd E ≤ X.firstMinimumSq x := by
  classical
  have hne : ∃ v ∈ X.Λ, v ≠ 0 := by
    by_contra h
    push Not at h
    have hle : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ ⊥ :=
      Submodule.span_le.mpr fun v hv => by simp [h v hv]
    rw [X.Λ_span] at hle
    have h1 : (fun _ : Fin r => (1 : E)) ∈ (⊥ : Submodule E (Fin r → E)) := hle Submodule.mem_top
    rw [Submodule.mem_bot] at h1
    have := congrFun h1 ⟨0, hr⟩
    simp at this
  have hΨ : ∃ τ, τ ∈ X.Ψ := by
    obtain ⟨σ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : σ0 ∈ X.Ψ
    · exact ⟨σ0, h⟩
    · refine ⟨ComplexEmbedding.conjugate σ0, ?_⟩
      rw [X.cmType, ComplexEmbedding.involutive_conjugate E σ0]
      exact h
  have hbound : ∀ v ∈ X.Λ, v ≠ 0 →
      2 * (I2.PT.f E : ℝ) / I2.PT.rd E ≤ ∑ τ, X.c τ * X.maj x τ (FD.Data.emb τ.1 v) := by
    intro v hv hv0
    have hemb : ∀ τ : X.Ψ, FD.Data.emb τ.1 v ≠ 0 := by
      intro τ h
      apply hv0
      funext a
      have := congrFun h a
      simpa [FD.Data.emb] using this
    set y := X.ξ0 * FD.herm X.Gm v v with hy
    have hterm : ∀ τ : X.Ψ, X.c τ * X.maj x τ (FD.Data.emb τ.1 v) = 2 * ‖τ.1 y‖ := by
      intro τ
      obtain ⟨s, hs, hseq⟩ := hermC_neg X h0 τ (hemb τ)
      rw [FD.Data.maj, posPart_eq_zero X h0 x τ, hseq, FD.Data.c, hy, map_mul, norm_mul,
        map_herm, hseq]
      simp [abs_of_pos hs]
      ring
    have hh0 : FD.herm X.Gm v v ≠ 0 := by
      intro h
      obtain ⟨τ0, hτ0⟩ := hΨ
      obtain ⟨s, hs, hseq⟩ := hermC_neg X h0 ⟨τ0, hτ0⟩ (hemb ⟨τ0, hτ0⟩)
      rw [← map_herm, h, map_zero] at hseq
      have := congrArg Complex.re hseq
      simp at this
      linarith
    have hy0 : y ≠ 0 := mul_ne_zero X.ξ0_ne hh0
    have htr : ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (y * a) = k := by
      intro a
      obtain ⟨k, hk⟩ := hint (a • v) (X.Λ.smul_mem a hv) v hv
      refine ⟨k, ?_⟩
      rw [← hk]
      congr 1
      simp only [hy, FD.herm, Pi.smul_apply, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hc : (algebraMap (𝓞 E) E) a = (a : E) := rfl
      rw [Algebra.smul_def, hc]
      ring
    have hsum : ∑ τ, X.c τ * X.maj x τ (FD.Data.emb τ.1 v) = ∑ σ : E →+* ℂ, ‖σ y‖ := by
      rw [Finset.sum_congr rfl fun τ _ => hterm τ, sum_norm_eq_two_mul X y]
    rw [hsum]
    refine le_trans ?_ (finrank_div_rd_le htr hy0)
    have hrd0 : 0 ≤ I2.PT.rd E := Real.rpow_nonneg (abs_nonneg _) _
    have h2f : 2 * I2.PT.f E ≤ Module.finrank ℚ E := Nat.mul_div_le (Module.finrank ℚ E) 2
    have h2fR : 2 * (I2.PT.f E : ℝ) ≤ Module.finrank ℚ E := by exact_mod_cast h2f
    exact div_le_div_of_nonneg_right h2fR hrd0
  obtain ⟨v0, hv0, hv00⟩ := hne
  refine le_csInf ⟨_, v0, hv0, hv00, rfl⟩ ?_
  rintro t ⟨v, hv, hv0, rfl⟩
  exact hbound v hv hv0

theorem th_sq_le {q : ℕ} {R0 : ℝ} (hrd : 1 ≤ I2.PT.rd E) (hq : 0 < q)
    (hb : 1 ≤ I2.b0 (E := E) q R0) :
    I2.PT.f E * R0 ^ 2 * I2.RR (E := E) ^ 3 / q ≤ 2 * (I2.PT.f E : ℝ) / I2.PT.rd E := by
  have hRR : 1 ≤ I2.RR (E := E) := one_le_pow₀ hrd
  have hRRpos : 0 < I2.RR (E := E) := lt_of_lt_of_le zero_lt_one hRR
  have hrdpos : 0 < I2.PT.rd E := lt_of_lt_of_le zero_lt_one hrd
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hf : (0 : ℝ) ≤ I2.PT.f E := Nat.cast_nonneg _
  have hb' : (1 : ℝ) ≤ q / (R0 ^ 2 * I2.RR (E := E) ^ 4) := hb
  have hden : 0 < R0 ^ 2 * I2.RR (E := E) ^ 4 := by
    by_contra hle
    push Not at hle
    have : (q : ℝ) / (R0 ^ 2 * I2.RR (E := E) ^ 4) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hqpos.le hle
    linarith
  have hq' : R0 ^ 2 * I2.RR (E := E) ^ 4 ≤ q := by rwa [one_le_div hden] at hb'
  have hR0 : R0 ≠ 0 := by
    rintro rfl
    simp at hden
  have hRRne : I2.RR (E := E) ≠ 0 := hRRpos.ne'
  have hrdle : I2.PT.rd E ≤ I2.RR (E := E) := le_self_pow₀ hrd (by norm_num)
  have hnum : 0 ≤ (I2.PT.f E : ℝ) * R0 ^ 2 * I2.RR (E := E) ^ 3 :=
    mul_nonneg (mul_nonneg hf (sq_nonneg _)) (pow_nonneg hRRpos.le 3)
  calc (I2.PT.f E : ℝ) * R0 ^ 2 * I2.RR (E := E) ^ 3 / q
        ≤ I2.PT.f E * R0 ^ 2 * I2.RR (E := E) ^ 3 / (R0 ^ 2 * I2.RR (E := E) ^ 4) :=
        div_le_div_of_nonneg_left hnum hden hq'
    _ = I2.PT.f E / I2.RR (E := E) := by field_simp
    _ ≤ I2.PT.f E / I2.PT.rd E := div_le_div_of_nonneg_left hf hrdpos hrdle
    _ ≤ 2 * I2.PT.f E / I2.PT.rd E := by
        apply div_le_div_of_nonneg_right _ hrdpos.le
        linarith

theorem firstMinimumSq_ge_and_phi_eq_zero_definite :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : FD.Data E r), 0 < r → X.p0 = 0 → (∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * FD.herm X.Gm u v) = k) → ∀ x ∈ X.dom, 2 * (I2.PT.f E : ℝ) / I2.PT.rd E ≤ X.firstMinimumSq x ∧ ∀ (q : ℕ) (R0 : ℝ), 1 ≤ I2.PT.rd E → 0 < q → 1 ≤ I2.b0 (E := E) q R0 → I2.phiFD X (I2.th (E := E) q R0) x = 0 := by
  intro E _ _ _ r X hr h0 hint x _hx
  have hla := two_f_div_rd_le_la1sq X hr h0 hint x
  refine ⟨hla, fun q R0 hrd hq hb => ?_⟩
  have hth := th_sq_le (E := E) hrd hq hb
  unfold I2.phiFD
  rw [if_neg]
  rw [not_lt]
  unfold FD.Data.la1 I2.th
  exact Real.sqrt_le_sqrt (hth.trans hla)

end GlobalTheory.DefiniteMin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumSqGeAndPhiEqZeroDefiniteStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.la1sq_ge_two_f_div_rd_of_p0_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : FD.Data E r), 0 < r → X.p0 = 0 → (∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * FD.herm X.Gm u v) = k) → ∀ x ∈ X.dom, 2 * (I2.PT.f E : ℝ) / I2.PT.rd E ≤ X.firstMinimumSq x ∧ ∀ (q : ℕ) (R0 : ℝ), 1 ≤ I2.PT.rd E → 0 < q → 1 ≤ I2.b0 (E := E) q R0 → I2.phiFD X (I2.th (E := E) q R0) x = 0 := by
  first | exact @GlobalTheory.DefiniteMin.firstMinimumSq_ge_and_phi_eq_zero_definite | exact GlobalTheory.DefiniteMin.firstMinimumSq_ge_and_phi_eq_zero_definite | (intros; apply GlobalTheory.DefiniteMin.firstMinimumSq_ge_and_phi_eq_zero_definite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTorusWithSignUniformisationFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTorusWithSignUniformisationFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusSign

theorem cmHostUnit_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  have hne : H.bar H.rt ≠ H.rt := by
    intro h
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 : IsCMField.complexConj E (H.rt : E) = H.rt := by rw [← H.bar_eq, h]
    have h2 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
    rw [h1] at h2
    have h3 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
      simpa using this
    have him : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h2.symm
    have h4 := congrArg Complex.re h3
    simp [sq, him] at h4
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
  have hb : H.bar H.rt = -H.rt := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left hne
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add (f := _), map_one, hb, map_ofNat] at this
    rw [this]; ring
  have : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by rw [mul_add, H.two_weight_eq_one_add_root, h2]; ring
  exact mul_left_cancel₀ two_ne_zero this

theorem exists_torusAt_of_isom {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {r : ℕ} (X : FD.Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ)
    (isom : ∀ a b, ((D.EF a b : ℤ) : ℚ) =
      Algebra.trace ℚ E (-X.ξ0 * FD.herm X.Gm (φ a : Fin r → E) (φ b)))
    (x : FD.Frame X.Ψ r) (hx : x ∈ X.dom) : ∃ A : I2.TorusAt X x, A.w0 = H.w0 := by
  have key : ∀ a b, Algebra.trace ℚ E (X.ξ0 * FD.herm X.Gm (φ a : Fin r → E) (φ b)) = -((D.EF a b : ℤ) : ℚ) := by
    intro a b
    rw [isom, neg_mul, map_neg, neg_neg]
  refine GlobalTheory.torusAtExists E r X ?_ H.w0 ?_ x hx
  · intro f
    obtain ⟨a, ha⟩ := D.unimod.2 (-(f.comp φ.toLinearMap.toAddMonoidHom).toIntLinearMap)
    refine ⟨φ a, (φ a).2, fun v => ?_⟩
    obtain ⟨b, rfl⟩ := φ.surjective v
    rw [key, ha]
    simp
  · intro u hu v hv
    obtain ⟨a, ha⟩ := φ.surjective ⟨u, hu⟩
    obtain ⟨b, hb⟩ := φ.surjective ⟨v, hv⟩
    have hu' : u = (φ a : Fin r → E) := by rw [ha]
    have hv' : v = (φ b : Fin r → E) := by rw [hb]
    have hw : H.w0 - H.bar H.w0 = 1 - (H.bar H.w0 + H.bar H.w0) := by
      have := cmHostUnit_add_conj_eq_one H
      linear_combination this
    have hs : ((H.w0 : E) - FD.cc (H.w0 : E)) • v = (φ ((H.w0 - H.bar H.w0) • b) : Fin r → E) := by
      rw [map_smul, hb, FD.cc, ← H.bar_eq]
      funext i
      simp [Algebra.smul_def]
    refine ⟨D.EF a (H.bar H.w0 • b), ?_⟩
    rw [hs, hu', hv', key, key, hw, sub_smul, add_smul, one_smul, map_sub, map_add (f := _)]
    push_cast
    ring

theorem exists_torusAt_w0_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x), ∃ A : I2.TorusAt (U.X k) x.1, A.w0 = H.w0 := by
  intro E _ _ _ H Dw l Xo c σ r U k x W
  exact exists_torusAt_of_isom (W.F.Di (W.ik k)) (U.X k) (W.φ k) (W.isom k) x.1 x.2

end GlobalTheory.TorusSign
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTorusWithSignUniformisationFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusWithSign_uniformisationFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x), ∃ A : I2.TorusAt (U.X k) x.1, A.w0 = H.w0 := by
  first | exact @GlobalTheory.TorusSign.exists_torusAt_w0_eq | exact GlobalTheory.TorusSign.exists_torusAt_w0_eq | (intros; apply GlobalTheory.TorusSign.exists_torusAt_w0_eq <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem phiFD_eq_zero_at_last_index : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j), j = D.R.m → ∀ (DF q : ℕ) (R0 : ℝ), RunOK D.host.E D.R.r DF q R0 D.R.m → ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp), ∀ x ∈ ((T.U j σ).X k).dom, I2.phiFD ((T.U j σ).X k) (I2.th (E := D.host.E) q R0) x = 0 := by
  intro D T h j hj hjm DF q R0 hrun σ hσ k x hx
  have hu := h.unf j hj σ hσ
  have hq0 : (T.Q.Dw j).q = 0 := by
    rw [(h.pins.2.2.2 j hj).2.1, hjm]
    exact Nat.sub_self _
  have hp0 : ((T.U j σ).X k).p0 = 0 := ((hu.2.1 k).1).trans hq0
  obtain ⟨W⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unfAt hu k ⟨x, hx⟩
  have hint : ∀ u ∈ ((T.U j σ).X k).Λ, ∀ v ∈ ((T.U j σ).X k).Λ, ∃ z : ℤ,
      Algebra.trace ℚ D.host.E (((T.U j σ).X k).ξ0 * FD.herm ((T.U j σ).X k).Gm u v) = z := by
    intro u hu' v hv'
    have hEF := W.isom k ((W.φ k).symm ⟨u, hu'⟩) ((W.φ k).symm ⟨v, hv'⟩)
    simp only [LinearEquiv.apply_symm_apply] at hEF
    refine ⟨-((W.F.Di (W.ik k)).EF ((W.φ k).symm ⟨u, hu'⟩) ((W.φ k).symm ⟨v, hv'⟩)), ?_⟩
    rw [Int.cast_neg, hEF, neg_mul, map_neg, neg_neg]
  obtain ⟨A, -⟩ := GlobalTheory.T.exists_torusWithSign_uniformisationFrame _ _ _ _ _ _ _ _ (T.U j σ) k ⟨x, hx⟩ W
  obtain ⟨τ0⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ ((T.U j σ).X k).Ψ := by
    by_cases h1 : τ0 ∈ ((T.U j σ).X k).Ψ
    · exact ⟨τ0, h1⟩
    · refine ⟨NumberField.ComplexEmbedding.conjugate τ0, ?_⟩
      rw [((T.U j σ).X k).cmType]
      simpa using h1
  have hpos := A.dim_pos ⟨τ, hτ⟩
  have hneg := A.dim_neg ⟨τ, hτ⟩
  have hsum := A.T.dim_conj τ
  have hr : A.T.r = D.R.r := by
    simp only at hpos hneg
    omega
  obtain ⟨P, hPq, hPR, -⟩ := hrun A.T hr ⟨τ, by simp only at hpos; omega⟩
  have hr0 : 0 < D.R.r := by
    have h2m := D.R.two_le_m
    show 0 < D.R.k + D.R.m - 1
    omega
  refine (GlobalTheory.T.la1sq_ge_two_f_div_rd_of_p0_eq_zero D.host.E D.R.r ((T.U j σ).X k) hr0 hp0 hint x hx).2 q R0
    ?_ ?_ ?_
  · have h16 := P.hrd
    linarith
  · have h1q := P.hq
    omega
  · have hb := P.C2
    rwa [hPq, hPR] at hb

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.AuxiliaryCuspFormConstantMonotone
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonSectionsOfNoLeadingTerm
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin.NoPoint

section Abstract

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem subsingleton_sections_of_no_leadingTerm (G : GlobalFamilyData X ka wL wF) (hd : G.del = 0) (la : HeightOneSpectrum (𝓞 B.KO))
    (hB : InBasis G la) : Subsingleton (SectionSheafQuotient X la G.w wF) := by
  haveI : IsEmpty (Fin G.del) := by rw [hd]; infer_instance
  have h := hB.2
  rw [Set.range_eq_empty, Submodule.span_empty] at h
  exact (Submodule.subsingleton_iff (Kp X la G.N)).1 (subsingleton_of_bot_eq_top h)

theorem heights_of_del_zero (G : GlobalFamilyData X ka wL wF) (Q : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ) (hd : G.del = 0)
    (hB : ∀ la, InBasis G la) (hC : ∀ la, (Q la).InCurve) : Heights Q Gc PH Prw Pet := by
  haveI : IsEmpty (Fin G.del) := by rw [hd]; infer_instance
  have hI : ∀ la, (Q la).Ila = 0 := fun la => by
    haveI := subsingleton_sections_of_no_leadingTerm G hd la (hB la)
    unfold LocalPointData.Ila
    exact Module.length_eq_zero
  have hN : ∀ la, (Q la).Net = 0 := fun la => by
    haveI := subsingleton_sections_of_no_leadingTerm G hd la (hB la)
    haveI : Subsingleton (OsK X la G.w) := (hC la).2.2.1.subsingleton
    haveI : IsEmpty (PtsG G la) := ⟨fun ζ => ζ.isMaximal.ne_top (Subsingleton.elim _ _)⟩
    unfold LocalPointData.Net
    exact finsum_of_isEmpty _
  have hd' : (G.del : ℝ) = 0 := by rw [hd]; exact Nat.cast_zero
  refine ⟨fun la => by simp [hI la], by simp [hI, summable_zero], by simp [hI, hd'],
    fun _ => ⟨by simp [hN, summable_zero], by simp [hN, hd']⟩⟩

theorem inBasis_xplus (G : GlobalFamilyData X ka wL wF) (E : PtExt X) (hM : IntAtExt X E) (la : HeightOneSpectrum (𝓞 B.KO))
    (h : InBasis G la) : InBasis (gd2Xplus G E hM) la := h

theorem heights_xplus_of_del_zero (G : GlobalFamilyData X ka wL wF) (E : PtExt X) (hM : IntAtExt X E)
    (Q : ∀ la, LocalPointData (gd2Xplus G E hM) la) (Gc PH Prw Pet : ℝ) (hd : G.del = 0)
    (hB : ∀ la, InBasis G la) (hC : ∀ la, (Q la).InCurve) : Heights Q Gc PH Prw Pet :=
  heights_of_del_zero (gd2Xplus G E hM) Q Gc PH Prw Pet hd (fun la => inBasis_xplus G E hM la (hB la)) hC

end Abstract


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem heights_no_point : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (Q : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la) (Gc PH Prw Pet : ℝ), G.del = 0 → (∀ la, InBasis G la) → (∀ la, (Q la).InCurve) → Heights Q Gc PH Prw Pet :=
  fun _ _ h j hj _ _ _ _ _ _ _ _ _ _ _ _ _ G Q Gc PH Prw Pet hd hB hC =>
    heights_xplus_of_del_zero G (extAll h j hj) (intAtExt_extAll h j hj) Q Gc PH Prw Pet hd hB hC

end GlobalTheory.RunJoin.NoPoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IInfLeOfCombBound
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.RunJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem iInf_le_of_combBound {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hjm : D.R.m ≤ j)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (cb : ℝ)
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ)
    (hspan : @Submodule.span (𝓞 (recB h.toLawsCore).KO) _ _ _ (WeightFamilies.Prov.modOC (recB h.toLawsCore) j wL)
      (Set.range G.w) = (recPJ h j hj).WWc S.sW wL)
    (hX : CombBound G S cb nus) :
    ∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal) := by
  rintro la _ ⟨y0, rfl⟩
  obtain ⟨y, hy⟩ := pt_realise h j hj la y0
  have hv : ∀ w (F : (recB h.toLawsCore).Cusp j w),
      (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y0 F.1 := fun w F => by
    rw [recPJ_vAt_inc, hy]
  have hd : (recPJ h j hj).depth S.sW wL la y = ⨅ k, vAtV y0 (G.w k).1 := by
    unfold PJ.depth
    rw [← hspan, iInf_span_eq (X := recPJ h j hj) G.w la ((recPJ h j hj).vAt la y)
      ((recPJ h j hj).vAt_zero la y) ((recPJ h j hj).vAt_add la y) ((recPJ h j hj).vAt_smul la y)
      (fun _ ha => vAdd_int_nonneg la ha)]
    simp only [hv]
  have h1 := (hX la y).2 hjm
  rw [hd] at h1
  exact h1

theorem combAlg_of_tiedW : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (ka wL wF : WeightFamilies.Wt D j) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (c Gc Prw : ℝ), G.TiedW S Gc Prw → CombBound G S c nus → (j < D.R.m → CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (c / (2 * (G.iet : ℝ)))) ∧ (j = D.R.m → ∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal)) := by
  intro D T h j hj ka wL wF S nus G c Gc Prw hW hX
  exact ⟨fun hjm => combAlg_of_combBound h j hj hjm G S c nus hW.1 hX,
    fun hjm => iInf_le_of_combBound h j hj hjm.ge G S c nus hW.1 hX⟩

end GlobalTheory.RunJoin
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunPrimeData

theorem runOK_of_pageOK {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {large₂ : SizeData₂ D} {H : KHyp}
    {C2 A2 CT : ℝ} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    (hP : PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0) :
    GlobalTheory.EtaAn.RunOK D.host.E D.R.r (DF wL) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + DF wL))) D.R.m := by
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hP.tie
  have htie : TieC ⟨1, 2, 1, 2, 1, 2, 1, 4, 7⟩ H 1 4 0 11 C2 A2 7 :=
    ⟨t1, t2, t3, t4, t5, rfl, rfl, t6, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  have hsupp : EtaleWeightGaps.PageSupp D large₂ B C2 A2 nW
      ⟨(((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 B.KO), 1, 1, 1⟩ wL := by
    refine ⟨hP.p13, fun σ => ?_, hP.frd, hP.r8, hP.df⟩
    have e : σ (((((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 B.KO)) : B.KO) =
        (((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : ℂ) := by
      rw [← map_natCast σ]
      exact congrArg σ (map_natCast (algebraMap (𝓞 B.KO) B.KO) _)
    change _ ≤ Real.log ‖σ (((((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 B.KO)) : B.KO)‖
    rw [e, Complex.norm_natCast, Nat.cast_pow, Real.log_pow, ← Nat.cast_mul]
    have h1 : 0 ≤ Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have h2 : (0 : ℝ) ≤ (DF wL : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg h2 h1]
  exact (GlobalTheory.RunParametersAtRecord.run_at_record D _ _ j X _ _ _ _ _ _ large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hP.hyp htie hP.page hsupp).1

theorem small_rows {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {large₂ : SizeData₂ D} {H : KHyp}
    {C2 A2 CT : ℝ} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    (hP : PageOK large₂ X H C2 A2 CT ka wL wF Tn nP nW h0) :
    0 ≤ large₂.sc.L ∧ 0 ≤ Zb D large₂ ∧ 0 ≤ cc D large₂ C2 A2 7 wL ∧ OPO large₂ B ∧ 1 ≤ WeightFamilies.PPv D large₂ 200000 2 ∧
      1 ≤ 200000 * zBase large₂ ^ 2 := by
  have hZ1 : 1 ≤ zBase large₂ := WeightFamilies.one_le_zBase large₂
  obtain ⟨hA, hS, -, -, -⟩ := hP.hyp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, hd⟩ := hS
  have hC : 0 ≤ C2 := by have := hd.1; rw [hP.tie.1] at this; linarith
  have hrd : 0 ≤ D.host.rdE := le_trans (by positivity) hP.frd
  have hL : 0 ≤ large₂.sc.L := by
    by_contra hn
    have h1 : (0 : ℝ) ≤ (D.R.f : ℝ) * (D.R.r : ℝ) := by positivity
    have h2 := mul_nonpos_of_nonneg_of_nonpos h1 (not_le.1 hn).le
    unfold zBase at hZ1
    linarith
  refine ⟨hL, le_trans zero_le_one hZ1, ?_, hO, ?_, by nlinarith⟩
  · unfold cc WeightFamilies.RRv WeightFamilies.PPv
    have := Real.rpow_nonneg hrd 7
    have := Real.rpow_nonneg (le_trans zero_le_one hZ1) A2
    positivity
  · unfold WeightFamilies.PPv
    have := Real.one_le_rpow hZ1 (by norm_num : (0 : ℝ) ≤ 2)
    linarith

theorem auxiliaryCuspFormConstant_monotone (D : D7) (j : ℕ) {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') : PI4 D j a b ≤ PI4 D j a' b' := by
  unfold PI4
  have : 2 * b / (WeightFamilies.dimY D j : ℝ) ≤ 2 * b' / (WeightFamilies.dimY D j : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  linarith


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_primeData_heights_of
    (hIndef : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j < D.R.m → FnAlgClosed (Xo := (T.Q.Xo j)) (c := T.Q.c) → 3 ≤ WeightFamilies.dimY D j → 0 < wL.n → (∀ la, InBasis G la) → ∀ (large₂ : SizeData₂ D) (Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL : ℝ) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (w2 : WeightFamilies.Wt D j) (t2 : (recB h.toLawsCore).Cusp j w2), G.TiedW S Gc Prw → G.TiedTh S Gc → (∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF) → IsG2 wL wF w2 → t2 ∈ (recB h.toLawsCore).Mlat j w2 → (recPlus h j hj).NonZeroComp w2 t2 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → WeightAlgebra.PN D large₂ ≤ PN' → LAMwAt large₂ (recB h.toLawsCore) j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) CL AL → LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0' (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL.size → 1 ≤ wL.size → (WeightAlgebra.DF wL : ℝ) ≤ wL.size → Real.log G.N + 1 / 2 ≤ Prw * (wL.size - 1) → Real.log (Module.finrank ℚ T.Q.c.F) ≤ POb → Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ POb → 1 ≤ PN' → 1 ≤ PP0' → 1 ≤ Gc → 1 ≤ PI4' → 1 ≤ Pet → 1 ≤ tableLineDegreeFive → 1 ≤ tableLineDegreeTwo → 1 ≤ Prw → 1 ≤ POb → PH = 2 * (PP0' + PN' + tableLineDegreeFive + tableLineDegreeTwo + PI4' + Prw) + Gc → ∀ (c th : ℝ) (w1 : WeightFamilies.Wt D j) (t1 : (recB h.toLawsCore).Cusp j w1), IsDoubledWeightWithShift wL w1 wL.n → t1 ∈ (recB h.toLawsCore).Mlat j w1 → (recPlus h j hj).NonZeroComp w1 t1 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w1 σ t1) ≤ 2 * PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → 0 < G.iet → G.et ∈ (recB h.toLawsCore).Mlat j _ → (recPlus h j hj).NonZeroComp _ G.et → (∀ σ, Real.log ((recB h.toLawsCore).supN j _ σ G.et) / G.iet ≤ Pet) → 0 ≤ c → c * (WeightAlgebra.g0 D : ℝ) ≤ 1 / 2 → CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (c / (2 * (G.iet : ℝ))) → (∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom → -Real.log (Real.sqrt (∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)) ≤ tableLineDegreeFive * (WeightAlgebra.DF wL : ℝ) + c * ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x) → EtArch h th tableLineDegreeTwo j G.iet G.et → Heights (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet)
    (hDef : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → ∀ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) → (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) → j = D.R.m → FnAlgClosed (Xo := (T.Q.Xo j)) (c := T.Q.c) → 3 ≤ WeightFamilies.dimY D j → 0 < wL.n → (∀ la, InBasis G la) → ∀ (large₂ : SizeData₂ D) (Gc PH Prw Pet PN' PP0' PI4' tableLineDegreeFive tableLineDegreeTwo POb CL AL : ℝ) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (w2 : WeightFamilies.Wt D j) (t2 : (recB h.toLawsCore).Cusp j w2), G.TiedW S Gc Prw → G.TiedTh S Gc → (∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF) → IsG2 wL wF w2 → t2 ∈ (recB h.toLawsCore).Mlat j w2 → (recPlus h j hj).NonZeroComp w2 t2 → (∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤ PI4' * (WeightFamilies.dimY D j : ℝ) * wL.size) → WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → WeightAlgebra.PN D large₂ ≤ PN' → LAMwAt large₂ (recB h.toLawsCore) j (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) CL AL → LamConst j large₂ CL AL (wsmul (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL) PP0' (8 * ((WeightFamilies.dimY D j + 2) * G.N) ^ 2 * (WeightFamilies.dimY D j + 1) * G.del * (1 + ⌈POb⌉₊)) wL.size → 1 ≤ wL.size → (WeightAlgebra.DF wL : ℝ) ≤ wL.size → Real.log G.N + 1 / 2 ≤ Prw * (wL.size - 1) → Real.log (Module.finrank ℚ T.Q.c.F) ≤ POb → Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ POb → 1 ≤ PN' → 1 ≤ PP0' → 1 ≤ Gc → 1 ≤ PI4' → 1 ≤ Pet → 1 ≤ tableLineDegreeFive → 1 ≤ tableLineDegreeTwo → 1 ≤ Prw → 1 ≤ POb → PH = 2 * (PP0' + PN' + tableLineDegreeFive + tableLineDegreeTwo + PI4' + Prw) + Gc → (∀ la, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) la, (⨅ k, v (G.w k).1) ≤ (nus la : EReal)) → (∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom → -Real.log (Real.sqrt (∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (G.w k').1 k x ^ 2)) ≤ tableLineDegreeFive * (WeightAlgebra.DF wL : ℝ)) → Heights (fun la => (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0)) Gc PH Prw Pet)
    (hData : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → (∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), BigAt h j hj hG G → BIRSt h j hj hG G) → 0 < wL.n → (j < D.R.m → (recPlus h j hj).NonZeroComp _ G.et) → ∀ (Gc Prw : ℝ) (Tn : ℕ), ∃ (y : ∀ la, PtsG G la → (extAll h j hj).Pt' la) (hw : ∀ la ζ, FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ (y la ζ)), (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InCurve) ∧ (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InTie S) ∧ (∀ la, (secQ (E := extAll h j hj) (hM := intAtExt_extAll h j hj) (y la) (fun ζ => (hw la ζ).toSecPt) g0).InLiftC S Gc Prw Tn)) :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (CL : ℝ), FnAlgClosed (Xo := (T.Q.Xo j)) (c := T.Q.c) → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → 0 < CL → (∀ w : WeightFamilies.Wt D j, LAMwAt large₂ (recB h.toLawsCore) j w CL 2) → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → G.TiedTh S (gcR large₂ (recB h.toLawsCore)) → (∀ la, InBasis G la) → Real.log G.del ≤ 1041 * Zb D large₂ ^ 3 → CombBound G S (cc D large₂ C2 A2 7 wL) nus → ∃ Qf : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la, (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S (gcR large₂ (recB h.toLawsCore)) (prwR large₂) Tn) ∧ Heights Qf (gcR large₂ (recB h.toLawsCore)) (phR large₂ (recB h.toLawsCore) CL wL) (prwR large₂) (WeightFamilies.PPv D large₂ 200000 2) := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus CL hAlg hP hC hCL hLam G hGen hEta hTh hBas hdel hComb
  obtain ⟨hG, hT⟩ := GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ (T.Q.Xo j) T.Q.c
  haveI : Finite (Comp (T.Q.Xo j) T.Q.c) := CompFin.finite_comp _ _
  letI : Fintype (Comp (T.Q.Xo j) T.Q.c) := Fintype.ofFinite _
  obtain ⟨g0, hcur⟩ := GlobalTheory.T.page_hypotheses_at_cusp D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus hG hP hC G hGen hEta
  have hinj := GlobalTheory.Reg.genValInj_record D T h j hj hG
  have hspl := GlobalTheory.Reg.compSplit_record D T h j hj hG
  have hbirA := fun ka wL wF G => (GlobalTheory.Reg.birSt_of_ratios_trdeg D T h j hj hG ka wL wF G).2
  have hbir := hbirA _ _ _ _ hcur.2.1
  obtain ⟨hL, hZ, hc0, hO, hPet, hP16⟩ := small_rows hP
  obtain ⟨hW, hN, hlogN, -, hlow⟩ := hGen
  obtain ⟨-, h3, hn, hn0, hDF, h2, hPO, -, hcg, -⟩ := GlobalTheory.RunJoin.lamConst_lamR_rows D _ _ j (recPJ h j hj) large₂ H C2 A2 CT
    ka wL wF Tn nP nW h0 CL G.N 1 hj hP hCL hN one_pos hlogN (by
      rw [Nat.cast_one, Real.log_one]; positivity)
  obtain ⟨y, hw, hc, ht, hl⟩ := hData D T h j hj hG (hT hG) ka wL wF
    (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) S g0 hcur hinj hspl hbir hbirA hn0
    (fun hjm => (hEta hjm).2.1.2) (gcR large₂ (recB h.toLawsCore)) (prwR large₂) Tn
  refine ⟨_, hc, ht, hl, ?_⟩
  rcases Nat.eq_zero_or_pos G.del with hd0 | hd0
  · exact GlobalTheory.RunJoin.NoPoint.heights_no_point D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S G _ _ _ _ _ hd0 hBas hc
  have hlc := (GlobalTheory.RunJoin.lamConst_lamR_rows D _ _ j (recPJ h j hj) large₂ H C2 A2 CT
    ka wL wF Tn nP nW h0 CL G.N G.del hj hP hCL hN hd0 hlogN hdel).1
  have hlN : Real.log G.N + 1 / 2 ≤ prwR large₂ * (wL.size - 1) := by
    have := hW.2.2.1
    unfold prwR
    linarith
  have hW' : G.TiedW S (gcR large₂ (recB h.toLawsCore)) (prwR large₂) :=
    ⟨hW.1, hW.2.1, by linarith, hW.2.2.2⟩
  obtain ⟨-, -, -, hH1, hH2, -, hH4, -⟩ := hC
  obtain ⟨-, -, -, -, -, -, PLam, lNc, hPL, hlNc, hI1, w2, hw2, t2, ht2, hnz2, hs2⟩ := hH4
  have hPI : PI4 D j PLam lNc ≤ max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) :=
    (auxiliaryCuspFormConstant_monotone D j hPL hlNc).trans (le_max_right _ _)
  have hsz : (0 : ℝ) ≤ wL.size := by linarith
  have hdm : (0 : ℝ) ≤ (WeightFamilies.dimY D j : ℝ) := Nat.cast_nonneg _
  have hs2' : ∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤
      max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) * (WeightFamilies.dimY D j : ℝ) * wL.size := fun σ =>
    (hs2 σ).trans (by gcongr)
  have hth' : ∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF := fun i => hH2.2.1 (hTh i).1
  have hO2 : Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ PO D large₂ := by
    have hd : (0 : ℝ) < |(NumberField.discr T.Q.c.F : ℝ)| :=
      abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero T.Q.c.F)
    rw [Real.log_rpow hd, one_div, inv_mul_eq_div]
    exact hO.2
  have hprw : 1 ≤ prwR large₂ := by unfold prwR; linarith
  obtain ⟨hA1, hA2⟩ := GlobalTheory.RunJoin.combAlg_of_tiedW D T h j hj ka wL wF S nus G _ _ _ hW hComb
  rcases lt_or_eq_of_le hj.2 with hjm | hjm
  · obtain ⟨hi, hec, -, hes, hea, hem⟩ := hEta hjm
    obtain ⟨w1, hw1, t1, ht1, hnz1, hs1⟩ := hI1 hjm
    refine hIndef D T h j hj hG ka wL wF _ S g0 hcur hinj hspl hbir y hw hc ht hjm hAlg h3 hn0 hBas large₂ _ _ _ _
      (max 1 (PN D large₂)) (lamR large₂ CL wL) _ (p14R wL) (200000 * zBase large₂ ^ 2) (PO D large₂) CL 2 nus w2 t2 hW' hTh hth' hw2 ht2
      hnz2 hs2' hH1 (le_max_right _ _) (hLam _) hlc (by linarith) hDF hlN hO.1 hO2 (le_max_left _ _) (le_max_left _ _)
      (le_max_left _ _) (le_max_left _ _) hPet (le_max_left _ _) hP16 hprw hPO rfl (cc D large₂ C2 A2 7 wL) (thR wL) w1 t1
      (hn ▸ hw1) ht1 hnz1 (fun σ => (hs1 σ).trans (by gcongr)) hi hem hec.2 hes hc0 hcg (hA1 hjm) hlow hea
  · refine hDef D T h j hj hG ka wL wF _ S g0 hcur hinj hspl hbir y hw hc ht hjm hAlg h3 hn0 hBas large₂ _ _ _ _
      (max 1 (PN D large₂)) (lamR large₂ CL wL) _ (p14R wL) (200000 * zBase large₂ ^ 2) (PO D large₂) CL 2 nus w2 t2 hW' hTh hth' hw2 ht2
      hnz2 hs2' hH1 (le_max_right _ _) (hLam _) hlc (by linarith) hDF hlN hO.1 hO2 (le_max_left _ _) (le_max_left _ _)
      (le_max_left _ _) (le_max_left _ _) hPet (le_max_left _ _) hP16 hprw hPO rfl (hA2 hjm) ?_
    intro σ hσ k x hx
    have h1 := hlow σ hσ k x hx
    have h2 : I2.phiFD ((T.U j σ).X k) (thR wL) x = 0 :=
      GlobalTheory.phiFD_eq_zero_at_last_index D T h j hj hjm _ _ _ (runOK_of_pageOK hP) σ hσ k x hx
    rw [h2, mul_zero, add_zero] at h1
    exact h1

end GlobalTheory.RunPrimeData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPrimeDataCurveLiftingHeightBounds
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunPrimeData


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_primeData_heights : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (CL : ℝ), FnAlgClosed (Xo := (T.Q.Xo j)) (c := T.Q.c) → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → 0 < CL → (∀ w : WeightFamilies.Wt D j, LAMwAt large₂ (recB h.toLawsCore) j w CL 2) → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → G.TiedTh S (gcR large₂ (recB h.toLawsCore)) → (∀ la, InBasis G la) → Real.log G.del ≤ 1041 * Zb D large₂ ^ 3 → CombBound G S (cc D large₂ C2 A2 7 wL) nus → ∃ Qf : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la, (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S (gcR large₂ (recB h.toLawsCore)) (prwR large₂) Tn) ∧ Heights Qf (gcR large₂ (recB h.toLawsCore)) (phR large₂ (recB h.toLawsCore) CL wL) (prwR large₂) (WeightFamilies.PPv D large₂ 200000 2) := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus CL hAlg hP hC hCL hLam G hGen hEta hTh hBas hdel hComb
  obtain ⟨hG, hT⟩ := GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ (T.Q.Xo j) T.Q.c
  haveI : Finite (Comp (T.Q.Xo j) T.Q.c) := CompFin.finite_comp _ _
  letI : Fintype (Comp (T.Q.Xo j) T.Q.c) := Fintype.ofFinite _
  obtain ⟨g0, hcur⟩ := GlobalTheory.T.page_hypotheses_at_cusp D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus hG hP hC G hGen hEta
  have hinj := GlobalTheory.Reg.genValInj_record D T h j hj hG
  have hspl := GlobalTheory.Reg.compSplit_record D T h j hj hG
  have hbirA := fun ka wL wF G => (GlobalTheory.Reg.birSt_of_ratios_trdeg D T h j hj hG ka wL wF G).2
  have hbir := hbirA _ _ _ _ hcur.2.1
  obtain ⟨hL, hZ, hc0, hO, hPet, hP16⟩ := small_rows hP
  obtain ⟨hW, hN, hlogN, -, hlow⟩ := hGen
  obtain ⟨-, h3, hn, hn0, hDF, h2, hPO, -, hcg, -⟩ := GlobalTheory.RunJoin.lamConst_lamR_rows D _ _ j (recPJ h j hj) large₂ H C2 A2 CT
    ka wL wF Tn nP nW h0 CL G.N 1 hj hP hCL hN one_pos hlogN (by
      rw [Nat.cast_one, Real.log_one]; positivity)
  obtain ⟨y, hw, hc, ht, hl⟩ := GlobalTheory.T.exists_realisationPrimeData_curve_lifting D T h j hj hG (hT hG) ka wL wF
    (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) S g0 hcur hinj hspl hbir hbirA hn0
    (fun hjm => (hEta hjm).2.1.2) (gcR large₂ (recB h.toLawsCore)) (prwR large₂) Tn
  refine ⟨_, hc, ht, hl, ?_⟩
  rcases Nat.eq_zero_or_pos G.del with hd0 | hd0
  · exact GlobalTheory.RunJoin.NoPoint.heights_no_point D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S G _ _ _ _ _ hd0 hBas hc
  have hlc := (GlobalTheory.RunJoin.lamConst_lamR_rows D _ _ j (recPJ h j hj) large₂ H C2 A2 CT
    ka wL wF Tn nP nW h0 CL G.N G.del hj hP hCL hN hd0 hlogN hdel).1
  have hlN : Real.log G.N + 1 / 2 ≤ prwR large₂ * (wL.size - 1) := by
    have := hW.2.2.1
    unfold prwR
    linarith
  have hW' : G.TiedW S (gcR large₂ (recB h.toLawsCore)) (prwR large₂) :=
    ⟨hW.1, hW.2.1, by linarith, hW.2.2.2⟩
  obtain ⟨-, -, -, hH1, hH2, -, hH4, -⟩ := hC
  obtain ⟨-, -, -, -, -, -, PLam, lNc, hPL, hlNc, hI1, w2, hw2, t2, ht2, hnz2, hs2⟩ := hH4
  have hPI : PI4 D j PLam lNc ≤ max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) :=
    (auxiliaryCuspFormConstant_monotone D j hPL hlNc).trans (le_max_right _ _)
  have hsz : (0 : ℝ) ≤ wL.size := by linarith
  have hdm : (0 : ℝ) ≤ (WeightFamilies.dimY D j : ℝ) := Nat.cast_nonneg _
  have hs2' : ∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤
      max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) * (WeightFamilies.dimY D j : ℝ) * wL.size := fun σ =>
    (hs2 σ).trans (by gcongr)
  have hth' : ∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF := fun i => hH2.2.1 (hTh i).1
  have hO2 : Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ PO D large₂ := by
    have hd : (0 : ℝ) < |(NumberField.discr T.Q.c.F : ℝ)| :=
      abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero T.Q.c.F)
    rw [Real.log_rpow hd, one_div, inv_mul_eq_div]
    exact hO.2
  have hprw : 1 ≤ prwR large₂ := by unfold prwR; linarith
  obtain ⟨hA1, hA2⟩ := GlobalTheory.RunJoin.combAlg_of_tiedW D T h j hj ka wL wF S nus G _ _ _ hW hComb
  rcases lt_or_eq_of_le hj.2 with hjm | hjm
  · obtain ⟨hi, hec, -, hes, hea, hem⟩ := hEta hjm
    obtain ⟨w1, hw1, t1, ht1, hnz1, hs1⟩ := hI1 hjm
    refine GlobalTheory.T.heightInequalities_indefinite_liftIndex D T h j hj hG ka wL wF _ S g0 hcur hinj hspl hbir y hw hc ht hjm hAlg h3 hn0 hBas large₂ _ _ _ _
      (max 1 (PN D large₂)) (lamR large₂ CL wL) _ (p14R wL) (200000 * zBase large₂ ^ 2) (PO D large₂) CL 2 nus w2 t2 hW' hTh hth' hw2 ht2
      hnz2 hs2' hH1 (le_max_right _ _) (hLam _) hlc (by linarith) hDF hlN hO.1 hO2 (le_max_left _ _) (le_max_left _ _)
      (le_max_left _ _) (le_max_left _ _) hPet (le_max_left _ _) hP16 hprw hPO rfl (cc D large₂ C2 A2 7 wL) (thR wL) w1 t1
      (hn ▸ hw1) ht1 hnz1 (fun σ => (hs1 σ).trans (by gcongr)) hi hem hec.2 hes hc0 hcg (hA1 hjm) hlow hea
  · refine GlobalTheory.T.heightInequality_definite_liftIndex D T h j hj hG ka wL wF _ S g0 hcur hinj hspl hbir y hw hc ht hjm hAlg h3 hn0 hBas large₂ _ _ _ _
      (max 1 (PN D large₂)) (lamR large₂ CL wL) _ (p14R wL) (200000 * zBase large₂ ^ 2) (PO D large₂) CL 2 nus w2 t2 hW' hTh hth' hw2 ht2
      hnz2 hs2' hH1 (le_max_right _ _) (hLam _) hlc (by linarith) hDF hlN hO.1 hO2 (le_max_left _ _) (le_max_left _ _)
      (le_max_left _ _) (le_max_left _ _) hPet (le_max_left _ _) hP16 hprw hPO rfl (hA2 hjm) ?_
    intro σ hσ k x hx
    have h1 := hlow σ hσ k x hx
    have h2 : I2.phiFD ((T.U j σ).X k) (thR wL) x = 0 :=
      GlobalTheory.phiFD_eq_zero_at_last_index D T h j hj hjm _ _ _ (runOK_of_pageOK hP) σ hσ k x hx
    rw [h2, mul_zero, add_zero] at h1
    exact h1


end GlobalTheory.RunPrimeData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPrimeDataCurveLiftingHeightBoundsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeData_curve_lifting_heightBounds : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (CL : ℝ), FnAlgClosed (Xo := (T.Q.Xo j)) (c := T.Q.c) → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → 0 < CL → (∀ w : WeightFamilies.Wt D j, LAMwAt large₂ (recB h.toLawsCore) j w CL 2) → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → G.TiedTh S (gcR large₂ (recB h.toLawsCore)) → (∀ la, InBasis G la) → Real.log G.del ≤ 1041 * Zb D large₂ ^ 3 → CombBound G S (cc D large₂ C2 A2 7 wL) nus → ∃ Qf : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la, (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S (gcR large₂ (recB h.toLawsCore)) (prwR large₂) Tn) ∧ Heights Qf (gcR large₂ (recB h.toLawsCore)) (phR large₂ (recB h.toLawsCore) CL wL) (prwR large₂) (WeightFamilies.PPv D large₂ 200000 2) := by
  first | exact @GlobalTheory.RunPrimeData.exists_primeData_heights | exact GlobalTheory.RunPrimeData.exists_primeData_heights | (intros; apply GlobalTheory.RunPrimeData.exists_primeData_heights <;> assumption)
end
