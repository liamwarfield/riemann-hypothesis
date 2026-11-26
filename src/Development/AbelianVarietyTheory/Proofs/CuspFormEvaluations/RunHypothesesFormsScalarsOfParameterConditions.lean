module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaSeriesSpanCuspFormsWeight
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependent
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIntegralAuxiliaryCuspFormsSupBound
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormShortGeneratorEvalLeOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ScaledThetaLatticeGeneratorsNoCommonZero
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledRunLatticesInSupLatticesProof
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralFormsLogSupNormLowerBoundAbsolute
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthSumRecord

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNonzeroBoundedSupBound
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFiniteSpanningShortGeneratorsSmallSupNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortGeneratorMemSpanSmallSupNormShortGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogSupNormShortThetaGeneratorLe
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogSupNormShortThetaGeneratorLe
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn


set_option maxHeartbeats 800000 in
theorem log_sup_short_generator_le : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (g : T.R j), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j w.n).l₂.M → Λ.LevOK N (T.dδ j w.n).l₂.M → AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0 → P ∈ harmL T.Q.c Λ (wtA w) → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g → g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → ∀ (σ : T.Q.c.F →+* ℂ) (ℓ : ℝ), 0 ≤ ℓ → l1At σ P ≤ Real.exp ℓ → Real.log (T.Ns j w σ g) ≤ ℓ + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L := by
  intro hCh D T hT hG large₂ j hj w hRows hL hr hLast hSh hA Λ N x0 P g hU hTb hTM hLev hX hP hS hg σ ℓ hℓ hl1
  obtain ⟨hfd, hrd, hrd1, hf1, hr1, hxi, hDF, habs, hc, hlie, hlA, hpde, hpde', hl1g⟩ := GlobalTheory.T.unitaryDatumNumbers_for_supBounds D T hT j hj w
  have hRw := hRows
  obtain ⟨-, hlrd, -, -, hlf, hlp, hlp', hlDF, hln⟩ := hRows
  set σ' := goodOf T.Q.c σ with hσ'
  have hgood : GoodEmb T.Q.c σ' := goodEmb_goodOf _ σ
  have hgC : g ∈ T.C j w :=
    hSh.8 j hj (wtA w) w.n (dom_wtA w) hLast (dom_wtA w) hLast ⟨hg, Λ, N, x0, P, hU, hTb, hTM, hLev, hX, hP, hS⟩
  obtain ⟨Cls, _, _, δ, gdet, hcmp⟩ := hSh.6 j hj w.n
  have hUC : GlobalTheory.Dict.UnitC (T.dδ j w.n) := FiniteOrderRule.unitC_of_cmp _ _ _ _ _ _ _ _ Cls δ gdet hcmp
  obtain ⟨p, hp, hpd⟩ := hSh.4
  have hpdw : (T.dδ j w.n).pd = p := hpd j hj w.n
  have hp0 : 0 < p := by rcases hp with rfl | rfl <;> assumption
  have hlogp : Real.log p ≤ large₂.sc.L := by rcases hp with rfl | rfl <;> assumption
  obtain ⟨ph, ψ, xψ, -, hpin, -⟩ := hSh.5 j hj w.n hr
  have hunf : IsUnf (T.U j σ') := hT.unf j hj σ' hgood
  have hNs : T.Ns j w σ g = lieFac (T.Q.Dw j) (xiR D) (wtA w) *
      supN (T.U j σ').X (laU (T.U j σ') (wtA w) w.n) (rdU (T.U j σ') g) := rfl
  rw [hNs, hlie]
  set S := supN (T.U j σ').X (laU (T.U j σ') (wtA w) w.n) (rdU (T.U j σ') g) with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; unfold supN; exact ENNReal.toReal_nonneg
  have hL0 : (0:ℝ) ≤ large₂.sc.L := by linarith
  have ha0 : (0:ℝ) ≤ absA w := by rw [habs]; positivity
  rcases hS0.eq_or_lt with hS00 | hSpos
  · rw [← hS00, mul_zero, Real.log_zero]
    positivity
  obtain ⟨k, xf, -, hortho, hSle, hla, hlog⟩ :=
    GlobalTheory.T.cuspForm_halfSup_at_orthonormalFrame_firstMin D T hT hG large₂ j hj w hRw hL hr hLast σ' hgood g hgC hSpos
  set lam := Real.sqrt (((T.U j σ').X k).firstMinimumSq xf.1) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr hla
  have hlam2 : lam ^ 2 = ((T.U j σ').X k).firstMinimumSq xf.1 := Real.sq_sqrt hla.le
  have hv := GlobalTheory.T.norm_short_generator_eval_le_orthonormal_frame hCh D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c σ' D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ')) ((Formalism.L2.PjFree.goodEmb_iff σ').mpr hgood)
    ((Formalism.L2.PjFree.isUnf_ofPj _).mpr hunf) hr1 (2 * xiR D) (by linarith) (hc σ' hgood) (wtA w) w.n
    (dom_wtA w) hr (T.dδ j w.n) (hSh.2 j hj w.n) (by rw [hpdw]; exact hp0) hlA hA (hSh.3 j hj w.n)
    ⟨ph, ψ, xψ, hpin⟩ hUC Λ N x0 P g hU hTM hLev (hSh.1 j hj w.n (hT.kPsi j hj) Λ hU hTb) hP hS
    k xf hortho lam hlam0 hlam2.le
  have hp1eq : (∑ m ∈ P.support, ‖σ' (P.coeff m)‖) = l1At σ P := hl1g _ σ P
  rw [hfd, hp1eq] at hv
  have hcle : ((T.dδ j w.n).pd : ℝ) ^ (D.R.f * D.R.r * w.n) ≤
      Real.exp (D.R.f * D.R.r * w.n * large₂.sc.L) := by
    rw [hpdw]
    have hp' : (0:ℝ) < p := by exact_mod_cast hp0
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hp']
    apply Real.exp_le_exp.mpr
    push_cast
    have hfrn : (0:ℝ) ≤ D.R.f * D.R.r * w.n := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlogp hfrn]
  have hp1 : 0 ≤ l1At σ P := by unfold l1At; exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  exact GlobalTheory.log_exp_mul_le_of_generator_sup_bound D.R.f D.R.r w.n (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w))
    large₂.sc.L ℓ (absA w) (rdE D.host.E) lam (2 * xiR D) _ S _ (l1At σ P) hL hf1 hr1 hr
    (by rw [habs]; exact_mod_cast hDF) (by rw [habs]; exact hlDF) hln hlf hrd1 (by rw [hrd]; exact hlrd)
    hlam0 (by rw [hlam2]; exact hlog) (by linarith) hℓ hp1 hl1 (by positivity) hcle hS0 hSle hv

end GlobalTheory.RunIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogSupNormShortThetaGeneratorLeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_supNorm_shortThetaGenerator_le : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (g : T.R j), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j w.n).l₂.M → Λ.LevOK N (T.dδ j w.n).l₂.M → AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0 → P ∈ harmL T.Q.c Λ (wtA w) → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g → g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → ∀ (σ : T.Q.c.F →+* ℂ) (ℓ : ℝ), 0 ≤ ℓ → l1At σ P ≤ Real.exp ℓ → Real.log (T.Ns j w σ g) ≤ ℓ + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L := by
  first | exact @GlobalTheory.RunIn.log_sup_short_generator_le | exact GlobalTheory.RunIn.log_sup_short_generator_le | (intros; apply GlobalTheory.RunIn.log_sup_short_generator_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortGeneratorMemSpanSmallSupNormShortGenerators
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem fg_of_trivAt_even {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) {bad : ℕ}
    (h2 : 2 ∣ bad) (h : Λ.TrivAt bad) : Λ.La.FG := by
  obtain ⟨k, hk, hle, -⟩ := h
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hk
    omega
  have hstd : (stdLat E n).FG := by
    unfold stdLat
    exact Submodule.fg_pi fun _ => Submodule.fg_unit 1
  have hkO : (k : 𝓞 E) ≠ 0 := by exact_mod_cast hk0
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 E) (Fin n → E) (k : 𝓞 E)) :=
    LinearMap.lsmul_injective hkO
  refine Submodule.fg_of_fg_map_injective _ hinj ?_
  have hN := isNoetherian_of_fg_of_noetherian _ hstd
  refine isNoetherian_submodule.1 hN _ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact hle (Submodule.smul_mem_smul (Ideal.subset_span rfl) hv)

theorem sh_mem_span_small : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ g ∈ T.sh j w, g ∈ Submodule.span T.Q.c.F {g' : T.R j | g' ∈ T.sh j w ∧ ∀ σ, Real.log (T.Ns j w σ g') ≤ 400 * Zb D large₂ * w.size} := by
  intro hCI D T h hG large₂ j hj w hP hL hrn hlp hS hA g hg
  obtain ⟨hgs, Λ, N, x0, P, hU, hT1, hT2, hLev, hAdm, hPh, hR⟩ := hg
  obtain ⟨-, -, -, -, -, hfd, -, hrd, hfr, hf1, -⟩ := GlobalTheory.T.exists_clearing_integers_principalDatum_host D large₂.sc.L hL hP.2.1 hP.2.2.1 hP.2.2.2.1
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := ((GlobalTheory.T.numerical_consequences_of_pins D T.Q h.pins).2.2.2.2.2.2 j hj).1
  have hfg : Λ.La.FG := fg_of_trivAt_even Λ (by
    unfold badN
    have h2 : 2 ∣ D.host.QS := (D.host.mem_small_iff.1 D.host.two_mem_small).2
    exact ((h2.mul_right _).mul_right _).mul_right _) hT1
  have hdf : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ (Formalism.MainNotions.WeightAlgebra.DF w : ℝ) := by
    exact_mod_cast ReciprocityTheory.ChartRestriction.G.PullbackSections.DF_wtA_le T j w
  have e : ((Formalism.MainNotions.WeightAlgebra.DF w : ℕ) : ℝ) = absA w := by
    unfold absA Formalism.MainNotions.WeightAlgebra.DF degP
    push_cast
    rfl
  obtain ⟨S, hS1, hS2, -⟩ := GlobalTheory.T.exists_short_harmonic_family_unimodular D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c w.n Λ hU hfg (hr ▸ hrn) (wtA w)
    large₂.sc.L hL hrd (by rw [hfd]; exact hP.2.2.2.2.1)
    ((Real.log_le_log (by positivity) (by linarith)).trans hP.2.2.2.2.2.2.2.1) hP.2.2.2.2.2.2.2.2
  obtain ⟨m, cf, Q, hsum⟩ := Submodule.mem_span_set'.1 (hS2 P hPh.1)
  have hQ : ∀ i, (Q i).1 ∈ harmL T.Q.c Λ (wtA w) := fun i => (hS1 _ (Q i).2).1
  choose gs hgs1 hgs2 using fun i =>
    (hS.shTot j hj (wtA w) w.n (dom_wtA w) Λ N x0 (Q i).1 hU hT1 hT2 hLev hAdm (hQ i)).2
  have hlin := GlobalTheory.T.shortThetaRule_linear_in_harmonic_polynomial hCI D T h hS j hj w Λ N x0 hU hT2 hLev m cf (fun i => (Q i).1) g gs hQ hgs hgs1
    (by rw [hsum]; exact hR) hgs2
  rw [hlin]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨⟨hgs1 i, Λ, N, x0, (Q i).1, hU, hT1, hT2, hLev, hAdm, hQ i, hgs2 i⟩, fun σ => ?_⟩)
  have hL0 : 0 ≤ large₂.sc.L := by linarith
  have hA0 : 0 ≤ absA w := by rw [← e]; positivity
  have hb : Real.log (l1At σ (Q i).1) ≤ 140 * D.R.r * large₂.sc.L * absA w := by
    refine ((hS1 _ (Q i).2).2 σ).trans ?_
    rw [hr, ← e]
    exact mul_le_mul_of_nonneg_left hdf (by positivity)
  have hl1 : l1At σ (Q i).1 ≤ Real.exp (140 * D.R.r * large₂.sc.L * absA w) :=
    (Real.le_exp_log _).trans (Real.exp_le_exp.2 hb)
  have hsup := GlobalTheory.T.log_supNorm_shortThetaGenerator_le hCI D T h hG large₂ j hj w hP hL hrn (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hlp) hS hA
    Λ N x0 (Q i).1 (gs i) hU hT1 hT2 hLev hAdm (hQ i) (hgs2 i) (hgs1 i) σ _ (by positivity) hl1
  exact hsup.trans (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j w 0 hL (by omega)).1

end GlobalTheory.RunIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortGeneratorMemSpanSmallSupNormShortGeneratorsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortGenerator_mem_span_small_supNorm_shortGenerators : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ g ∈ T.sh j w, g ∈ Submodule.span T.Q.c.F {g' : T.R j | g' ∈ T.sh j w ∧ ∀ σ, Real.log (T.Ns j w σ g') ≤ 400 * Zb D large₂ * w.size} := by
  first | exact @GlobalTheory.RunIn.sh_mem_span_small | exact GlobalTheory.RunIn.sh_mem_span_small | (intros; apply GlobalTheory.RunIn.sh_mem_span_small <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem exists_finset_span_top_of_span {O K R : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup R]
    [Module K R] [Module O R] [IsScalarTower O K R] (C : Submodule K R) [FiniteDimensional K C] (s A : Set R)
    (hA : A ⊆ C) (hs : ∀ g ∈ s, g ∈ Submodule.span K A)
    (htop : Submodule.span K
      (((Submodule.span O s).comap (C.subtype.restrictScalars O) : Submodule O C) : Set C) = ⊤) :
    ∃ Sh : Finset C, (∀ g ∈ Sh, (g : R) ∈ A) ∧ Submodule.span K (Sh : Set C) = ⊤ := by
  classical
  set A' : Set C := {x | (x : R) ∈ A} with hA'
  have hsub : ∀ x : C, (x : R) ∈ Submodule.span K A → x ∈ Submodule.span K A' := by
    intro x hx
    have himg : (C.subtype '' A') = A := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨⟨y, hA hy⟩, hy, rfl⟩
    rw [← himg, ← Submodule.map_span] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := Subtype.ext hyx
    rwa [← hyx']
  have htop' : Submodule.span K A' = ⊤ := by
    rw [eq_top_iff, ← htop, Submodule.span_le]
    intro x hx
    apply hsub
    have hx' : (x : R) ∈ Submodule.span O s := hx
    exact (Submodule.span_le.mpr hs) (Submodule.span_le_restrictScalars O K s hx')
  obtain ⟨b, hbA, hbspan, hbli⟩ := exists_linearIndependent K A'
  have hbfin : b.Finite := hbli.setFinite
  refine ⟨hbfin.toFinset, ?_, ?_⟩
  · intro g hg
    exact hbA (hbfin.mem_toFinset.mp hg)
  · rw [hbfin.coe_toFinset, hbspan, htop']


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_short_family_small : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) w → ∃ Sh : Finset ((recB h.toLawsCore).Cusp j w), (∀ g ∈ Sh, g ∈ (recPJ h j hj).shortTh w ∧ ∀ σ, Real.log ((recB h.toLawsCore).supN j w σ g) ≤ 400 * Zb D large₂ * w.size) ∧ Submodule.span (recB h.toLawsCore).KO (Sh : Set ((recB h.toLawsCore).Cusp j w)) = ⊤ := by
  intro hC D T h hG large₂ j hj w hP hL hn hw hS hA hsp
  have hlp := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hw
  have hdom := dom_wtA w
  have hshC : T.sh j w ⊆ T.C j w := hS.shCusp j hj (wtA w) w.n hdom hlp hdom hlp
  have hsmall := GlobalTheory.T.shortGenerator_mem_span_small_supNorm_shortGenerators hC D T h hG large₂ j hj w hP hL hn hw hS hA
  unfold ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt at hsp
  simp only [recPJ, recB, mkX, mkB] at hsp ⊢
  unfold spanIn cutN cutR at *
  have hmemC : ∀ x, x ∈ T.C j w → x ∈ (T.C j w ⊓ ⨅ (_ : ¬InR D j), ⊥ : Submodule T.Q.c.F (T.R j)) := by
    intro x hx
    simp [hx, hj]
  have : FiniteDimensional T.Q.c.F (T.C j w) := h.toLawsCore.fd j hj w
  have : FiniteDimensional T.Q.c.F (T.C j w ⊓ ⨅ (_ : ¬InR D j), ⊥ : Submodule T.Q.c.F (T.R j)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hs : ∀ g ∈ T.sh j w, g ∈ Submodule.span T.Q.c.F
      {g' | g' ∈ (T.C j w ⊓ ⨅ (_ : ¬InR D j), ⊥ : Submodule T.Q.c.F (T.R j)) ∧ g' ∈ T.sh j w ∧
        ∀ σ, Real.log (T.Ns j w σ g') ≤ 400 * Zb D large₂ * w.size} := by
    intro g hg
    refine Submodule.span_mono ?_ (hsmall g hg)
    rintro x ⟨hx1, hx2⟩
    exact ⟨hmemC x (hshC hx1), hx1, hx2⟩
  obtain ⟨Sh, hShA, hShspan⟩ := exists_finset_span_top_of_span (O := 𝓞 T.Q.c.F)
    (T.C j w ⊓ ⨅ (_ : ¬InR D j), ⊥) (T.sh j w)
    {g' | g' ∈ (T.C j w ⊓ ⨅ (_ : ¬InR D j), ⊥ : Submodule T.Q.c.F (T.R j)) ∧ g' ∈ T.sh j w ∧
      ∀ σ, Real.log (T.Ns j w σ g') ≤ 400 * Zb D large₂ * w.size}
    (fun x hx => hx.1) hs hsp
  refine ⟨Sh, fun g hg => ?_, hShspan⟩
  obtain ⟨_, hgs, hgb⟩ := hShA g hg
  refine ⟨Submodule.subset_span hgs, fun σ => ?_⟩
  rw [if_pos hj]
  exact hgb σ

end GlobalTheory.RunIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNeZeroAndLogBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNeZeroAndLogBounded
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn.ScalSize

variable {D : D7} {j : ℕ}

theorem one_le_f (D : D7) : (1 : ℝ) ≤ D.R.f := by
  have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
  exact_mod_cast this

theorem one_le_r (D : D7) : (1 : ℝ) ≤ D.R.r := by
  have : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  exact_mod_cast this

theorem size_eq (w : WeightFamilies.Wt D j) :
    w.size = (WeightAlgebra.DF w : ℝ) + (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) + 1 := by
  unfold WeightFamilies.Wt.size WeightAlgebra.DF degP
  push_cast
  ring

theorem size_ge (w : WeightFamilies.Wt D j) : (WeightAlgebra.DF w : ℝ) + (D.R.f : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) + 1 ≤ w.size := by
  rw [size_eq]
  have h1 : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  have h2 : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 h2]

theorem n_le_size (w : WeightFamilies.Wt D j) : (w.n : ℝ) ≤ w.size := by
  have h := size_ge w
  have h1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le (one_le_f D) (one_le_r D)
  have h2 : (0 : ℝ) ≤ w.n := by positivity
  have h3 : (0 : ℝ) ≤ WeightAlgebra.DF w := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

theorem size_comb (T : ℕ) (wL wF : WeightFamilies.Wt D j) :
    (wadd wF (wsmul T wL)).size + T = T * wL.size + wF.size := by
  unfold WeightFamilies.Wt.size
  simp only [wadd, wsmul]
  push_cast
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  ring

theorem log_zOwn_le (p : ℕ) (hp : 0 < p) (w : WeightFamilies.Wt D j) :
    Real.log (zOwnP D p w : ℝ) ≤ 2 * Real.log p * w.size := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h := size_ge w
  have h3 : (0 : ℝ) ≤ WeightAlgebra.DF w := by positivity
  unfold zOwnP
  push_cast
  rw [Real.log_pow]
  push_cast
  have : (WeightAlgebra.DF w : ℝ) + 2 * D.R.f * D.R.r * w.n ≤ 2 * w.size := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this hl]

theorem lamStar_nonneg (w : WeightFamilies.Wt D j) : 0 ≤ lamStar D := by
  obtain ⟨-, -, h1, h2, -⟩ := GlobalTheory.RunIn.pPow_size D j w
  unfold lamStar
  linarith

noncomputable def comb (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) : 𝓞 B.KO :=
  (zOwnP D p G : 𝓞 B.KO) * sOf B hinj EX wL ^ T * sOf B hinj EX wF

theorem comb_eq (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) :
    (zOwnP D p G : 𝓞 B.KO) * nnW B hinj EX wL ^ T * nnW B hinj EX wF *
      (pPow D (T * c2 D wL + c2 D wF) (T * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF)
        (T * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF) : 𝓞 B.KO) = comb B hinj EX p G wL wF T := by
  unfold comb sOf pPow
  push_cast
  ring

theorem comb_ne_zero (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (hp : 0 < p)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) : comb B hinj EX p G wL wF T ≠ 0 := by
  unfold comb
  refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D B hinj EX j wL).1)) (GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D B hinj EX j wF).1
  exact Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne')

theorem log_comb_le (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (hp : 0 < p)
    (G wL wF : WeightFamilies.Wt D j) (T : ℕ) (σ : B.KO →+* ℂ) :
    Real.log ‖σ (comb B hinj EX p G wL wF T : B.KO)‖ ≤
      2 * Real.log p * G.size + lamStar D * (T * wL.size + wF.size) := by
  obtain ⟨hL0, hL⟩ := GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D B hinj EX j wL
  obtain ⟨hF0, hF⟩ := GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D B hinj EX j wF
  have hL1 := (hL σ).2.2.2
  have hF1 := (hF σ).2.2.2
  have nz : ∀ x : 𝓞 B.KO, x ≠ 0 → ‖σ (x : B.KO)‖ ≠ 0 := fun x hx => by
    rw [norm_ne_zero_iff, map_ne_zero]
    exact_mod_cast hx
  have hz : (zOwnP D p G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne')
  have e : ‖σ (comb B hinj EX p G wL wF T : B.KO)‖ =
      (zOwnP D p G : ℝ) * ‖σ (sOf B hinj EX wL : B.KO)‖ ^ T * ‖σ (sOf B hinj EX wF : B.KO)‖ := by
    unfold comb
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_natCast, norm_mul, norm_pow,
      Complex.norm_natCast]
  rw [e, Real.log_mul (mul_ne_zero hz (pow_ne_zero _ (nz _ hL0))) (nz _ hF0),
    Real.log_mul hz (pow_ne_zero _ (nz _ hL0)), Real.log_pow]
  have h1 := log_zOwn_le p hp G
  have hT : (0 : ℝ) ≤ T := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hL1 hT]

theorem log_comb_le' (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (hp : 0 < p)
    (wL wF : WeightFamilies.Wt D j) (hn : 1 ≤ wL.n) (T : ℕ) (σ : B.KO →+* ℂ) :
    Real.log ‖σ (comb B hinj EX p (wadd wF (wsmul T wL)) wL wF T : B.KO)‖ ≤
      2 * (lamStar D + 2 * Real.log p) * (wadd wF (wsmul T wL)).size := by
  have h := log_comb_le B hinj EX p hp (wadd wF (wsmul T wL)) wL wF T σ
  rw [← size_comb] at h
  have h1 := n_le_size (wadd wF (wsmul T wL))
  have h2 : T ≤ (wadd wF (wsmul T wL)).n := by
    simp only [wadd, wsmul]
    nlinarith
  have h3 : (T : ℝ) ≤ (wadd wF (wsmul T wL)).size := le_trans (by exact_mod_cast h2) h1
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hΛ := lamStar_nonneg wL
  have hs := (wadd wF (wsmul T wL)).one_le_size
  nlinarith [mul_le_mul_of_nonneg_left h3 hΛ, mul_nonneg hl (le_trans zero_le_one hs)]

theorem wt_eq {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} (hF : IsF' ka wL wF T nP) (hL : wL.n = nW)
    (hn : ka.n = nP + T * nW) : ka = wadd wF (wsmul T wL) := by
  obtain ⟨h1, h2, h3⟩ := hF
  obtain ⟨a, b, _, _, n, _⟩ := ka
  have e1 : a = (wadd wF (wsmul T wL)).aP := funext fun τ => funext fun i => by
    have := h2 τ i
    simp only [wadd, wsmul] at this ⊢
    zify
    linarith
  have e2 : b = (wadd wF (wsmul T wL)).aM := funext fun τ => funext fun i => by
    have := h3 τ i
    simp only [wadd, wsmul] at this ⊢
    zify
    linarith
  have e3 : n = (wadd wF (wsmul T wL)).n := by
    simp only [wadd, wsmul] at hn ⊢
    rw [h1, hL, hn]
  subst e1 e2 e3
  rfl

end GlobalTheory.RunIn.ScalSize


open GlobalTheory.RunIn.ScalSize in
theorem GlobalTheory.RunIn.scalOfP_size : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ), 0 < p → 1 ≤ nW → wL.n = nW → IsF' ka wL wF Tn nP → ka.n = nP + Tn * nW → (scalOfP B hinj EX p ka wL wF Tn).sF ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).s0 ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).sK ≠ 0 ∧ ∀ σ : B.KO →+* ℂ, (Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sW : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wL.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sF : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wF.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).s0 : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * (wadd wF (wsmul (WeightFamilies.dimY D j) wL)).size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sK : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * ka.size) := by
  intro D B hinj EX j p ka wL wF Tn nP nW hp hW hL hF hn
  have eF : (scalOfP B hinj EX p ka wL wF Tn).sF = comb B hinj EX p wF wL wF 0 := by
    unfold comb sOf
    simp only [scalOfP, pow_zero, mul_one, mul_assoc]
  have e0 : (scalOfP B hinj EX p ka wL wF Tn).s0 =
      comb B hinj EX p (wadd wF (wsmul (WeightFamilies.dimY D j) wL)) wL wF (WeightFamilies.dimY D j) := comb_eq ..
  have eK : (scalOfP B hinj EX p ka wL wF Tn).sK = comb B hinj EX p ka wL wF Tn := comb_eq ..
  have hn1 : 1 ≤ wL.n := hL ▸ hW
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  rw [eF, e0, eK, sW_eq_sOf]
  refine ⟨comb_ne_zero B hinj EX p hp _ _ _ _, comb_ne_zero B hinj EX p hp _ _ _ _,
    comb_ne_zero B hinj EX p hp _ _ _ _, fun σ => ⟨?_, ?_, log_comb_le' B hinj EX p hp wL wF hn1 _ σ, ?_⟩⟩
  · have h := ((GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D B hinj EX j wL).2 σ).2.2.2
    nlinarith [mul_nonneg hl (le_trans zero_le_one wL.one_le_size)]
  · have h := log_comb_le B hinj EX p hp wF wL wF 0 σ
    push_cast at h
    linarith
  · rw [wt_eq hF hL hn]
    exact log_comb_le' B hinj EX p hp wL wF hn1 _ σ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNeZeroAndLogBoundedStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.runScalars_ne_zero_and_log_bounded : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ), 0 < p → 1 ≤ nW → wL.n = nW → IsF' ka wL wF Tn nP → ka.n = nP + Tn * nW → (scalOfP B hinj EX p ka wL wF Tn).sF ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).s0 ≠ 0 ∧ (scalOfP B hinj EX p ka wL wF Tn).sK ≠ 0 ∧ ∀ σ : B.KO →+* ℂ, (Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sW : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wL.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sF : B.KO)‖ ≤ (lamStar D + 2 * Real.log p) * wF.size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).s0 : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * (wadd wF (wsmul (WeightFamilies.dimY D j) wL)).size ∧ Real.log ‖σ ((scalOfP B hinj EX p ka wL wF Tn).sK : B.KO)‖ ≤ 2 * (lamStar D + 2 * Real.log p) * ka.size) := by
  first | exact @GlobalTheory.RunIn.scalOfP_size | exact GlobalTheory.RunIn.scalOfP_size | (intros; apply GlobalTheory.RunIn.scalOfP_size <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortGeneratorsScaledThetaLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortGeneratorsScaledThetaLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem span_image_smul_top {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (c : K) (hc : c ≠ 0)
    (S : Set V) (hS : Submodule.span K S = ⊤) : Submodule.span K ((fun g => c • g) '' S) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  have key : ∀ x ∈ Submodule.span K S, c • x ∈ Submodule.span K ((fun g => c • g) '' S) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul e x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ e hx
  have hv : c⁻¹ • v ∈ Submodule.span K S := hS ▸ Submodule.mem_top
  simpa [smul_smul, hc] using key _ hv

theorem shortG_scaled : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (w : WeightFamilies.Wt D j) (s : 𝓞 B.KO) (Sh : Finset (B.Cusp j w)) (a b : ℝ), s ≠ 0 → 0 ≤ a → 0 ≤ b → (∀ σ : B.KO →+* ℂ, Real.log ‖σ (s : B.KO)‖ ≤ a) → (∀ g ∈ Sh, g ∈ X.shortTh w ∧ ∀ σ, Real.log (B.supN j w σ g) ≤ b) → Submodule.span B.KO (Sh : Set (B.Cusp j w)) = ⊤ → ShortG X w (X.Thc s w) (a + b + lamStar D * w.size) := by
  intro D B P j X w s Sh a b hs ha hb hsa hSh hspan
  classical

  let N : ℕ := D.host.g 0 * D.host.g 1
  let k : ℕ := D.R.f * D.R.r * w.n
  let t : 𝓞 B.KO := s * (N : 𝓞 B.KO) ^ k
  have hN1 : (1 : ℝ) ≤ N := by
    have h0 := (D.host.g_prime 0).one_lt
    have h1 := (D.host.g_prime 1).one_lt
    have : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    exact_mod_cast this
  have htK : ((t : 𝓞 B.KO) : B.KO) = (s : B.KO) * ((N : ℕ) : B.KO) ^ k := by
    simp [t]
  have hsK : (s : B.KO) ≠ 0 := fun h => hs (by exact_mod_cast h)
  have hNK : ((N : ℕ) : B.KO) ≠ 0 := by
    have : N ≠ 0 := by
      intro h; rw [h] at hN1; norm_num at hN1
    exact_mod_cast this
  have ht0 : ((t : 𝓞 B.KO) : B.KO) ≠ 0 := by
    rw [htK]; exact mul_ne_zero hsK (pow_ne_zero _ hNK)
  have hsm : ∀ g : B.Cusp j w, t • g = ((t : 𝓞 B.KO) : B.KO) • g := fun g =>
    (algebraMap_smul B.KO t g).symm
  have hlam : 0 ≤ Real.log N ∧ Real.log N ≤ lamStar D := by
    have h2 := (pPow_size D j w).2.2.1
    refine ⟨Real.log_nonneg hN1, ?_⟩
    unfold Formalism.MainNotions.WeightAlgebra.lamStar
    have : ((N : ℕ) : ℝ) = (D.host.g 0 : ℝ) * D.host.g 1 := by simp [N]
    rw [← this]; linarith
  have hk : (k : ℝ) ≤ w.size := by
    unfold WeightFamilies.Wt.size
    have hm : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    have hsum : 0 ≤ ∑ τ, ((∑ i, (w.aP τ i : ℝ)) + ∑ i, (w.aM τ i : ℝ)) := by positivity
    have : (k : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by
      calc (k : ℝ) = (D.R.f : ℝ) * 1 * (D.R.r : ℝ) * (w.n : ℝ) := by simp [k]
        _ ≤ _ := by gcongr
    linarith
  refine ⟨Sh.image fun g => t • g, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    simp only [PJ.Thc, PJ.scaled]
    refine Submodule.mem_map.mpr ⟨((N : 𝓞 B.KO) ^ k) • g, Submodule.mem_map.mpr ⟨g, (hSh g hg).1, by simp [N, k]⟩, ?_⟩
    simp only [t, mul_smul, LinearMap.smul_apply, LinearMap.id_apply]
  · have : ((Sh.image fun g => t • g : Finset (B.Cusp j w)) : Set (B.Cusp j w)) =
        (fun g => ((t : 𝓞 B.KO) : B.KO) • g) '' (Sh : Set (B.Cusp j w)) := by
      rw [Finset.coe_image]
      exact congrArg (· '' (Sh : Set (B.Cusp j w))) (funext hsm)
    rw [this]
    exact span_image_smul_top _ ht0 _ hspan
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
    apply WeightFamilies.meanLogSup_le
    intro σ
    rw [hsm, B.supN_smul, htK]
    have hσs : 0 < ‖σ (s : B.KO)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hsK)
    have hnorm : ‖σ ((s : B.KO) * ((N : ℕ) : B.KO) ^ k)‖ = ‖σ (s : B.KO)‖ * (N : ℝ) ^ k := by
      simp
    rw [hnorm]
    have hlog_s := hsa σ
    have hG := (hSh g hg).2 σ
    have hkN : (k : ℝ) * Real.log N ≤ lamStar D * w.size := by
      calc (k : ℝ) * Real.log N ≤ w.size * Real.log N := mul_le_mul_of_nonneg_right hk hlam.1
        _ ≤ w.size * lamStar D :=
            mul_le_mul_of_nonneg_left hlam.2 (by linarith [WeightFamilies.Wt.one_le_size w])
        _ = lamStar D * w.size := mul_comm _ _
    by_cases hg0 : B.supN j w σ g = 0
    · rw [hg0, mul_zero, Real.log_zero]
      have : 0 ≤ lamStar D * w.size :=
        mul_nonneg (hlam.1.trans hlam.2) (by linarith [WeightFamilies.Wt.one_le_size w])
      linarith
    · have hNk : (0 : ℝ) < (N : ℝ) ^ k := pow_pos (by linarith) _
      rw [Real.log_mul (mul_pos hσs hNk).ne' hg0, Real.log_mul hσs.ne' hNk.ne', Real.log_pow]
      linarith

end GlobalTheory.RunIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortGeneratorsScaledThetaLatticeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortGenerators_scaled_thetaLattice : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (w : WeightFamilies.Wt D j) (s : 𝓞 B.KO) (Sh : Finset (B.Cusp j w)) (a b : ℝ), s ≠ 0 → 0 ≤ a → 0 ≤ b → (∀ σ : B.KO →+* ℂ, Real.log ‖σ (s : B.KO)‖ ≤ a) → (∀ g ∈ Sh, g ∈ X.shortTh w ∧ ∀ σ, Real.log (B.supN j w σ g) ≤ b) → Submodule.span B.KO (Sh : Set (B.Cusp j w)) = ⊤ → ShortG X w (X.Thc s w) (a + b + lamStar D * w.size) := by
  first | exact @GlobalTheory.RunIn.shortG_scaled | exact GlobalTheory.RunIn.shortG_scaled | (intros; apply GlobalTheory.RunIn.shortG_scaled <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNonzeroBoundedSupBound
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem scalB_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → LawsSh T → (∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1) → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.OwnPr D p → FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) wF → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ((recPJ h j hj).wF0 wL wF) → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ka → ScalB large₂ (recPJ h j hj) H.C1 H.A1 (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn := by
  intro hCI D T h hGam hSh hA hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp hHP hRows hSpF hSpF0 hSpK
  obtain ⟨-, hSet, -, -, -⟩ := id hHP
  obtain ⟨hkaN, -, -, -, -, -, -, -, -, -, -, -, -, hnV, hIsL, hIsF, -, -, -, -, -, h40, -, -, -, -⟩ := hSet
  have hLn : wL.n = nW := hIsL.1
  have hkn : ka.n = nP + Tn * nW := hkaN.trans hnV
  have hp0 : 0 < p := by
    rcases hp with rfl | rfl
    · exact D.host.pde_prime.pos
    · exact D.host.pde'_prime.pos
  have hj1 : 1 ≤ j := hj.1
  obtain ⟨hL2, -, hr6, hlam, -, -⟩ := GlobalTheory.page_two_le_L_and_signs D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hHP hRows
  have hwb := GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj1 hHP
  have hsz := GlobalTheory.T.runScalars_ne_zero_and_log_bounded D (recB h.toLawsCore) hinj EX j p ka wL wF Tn nP nW hp0 (by omega) hLn hIsF hkn
  have hsW := GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds D (recB h.toLawsCore) hinj EX j wL
  have hWeq := GlobalTheory.RunIn.sW_eq_sOf (recB h.toLawsCore) hinj EX p ka wL wF Tn
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  have hZ : 0 ≤ Zb D large₂ := by
    unfold Zb
    exact mul_nonneg (by positivity) (by linarith)

  have hW : ∀ w ∈ ({wL, wF, (recPJ h j hj).wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w ∧ D.R.r ≤ w.n ∧ w.LastPos := by
    intro w hw
    obtain ⟨hdf, hn, hr, hlast⟩ := hwb.1 w hw
    exact ⟨GlobalTheory.pageRows_of_le D large₂ j ka w (by linarith) hdf hn hRows, hr, hlast⟩

  have hShort : ∀ (w : WeightFamilies.Wt D j) (s : 𝓞 (recB h.toLawsCore).KO) (c : ℝ),
      w ∈ ({wL, wF, (recPJ h j hj).wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)) →
      ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) w → s ≠ 0 → 0 ≤ c →
      c ≤ 2 * (lamStar D + 2 * Real.log p) * w.size →
      (∀ σ : (recB h.toLawsCore).KO →+* ℂ, Real.log ‖σ (s : (recB h.toLawsCore).KO)‖ ≤ c) →
      ShortG (recPJ h j hj) w ((recPJ h j hj).Thc s w) (Gc large₂ (recB h.toLawsCore) (1009 * Zb D large₂) p * w.size) := by
    intro w s c hw hsp hs hc0 hc hsc
    obtain ⟨hRw, hrw, hlw⟩ := hW w hw
    have hn8 : 0 < w.n := by omega
    obtain ⟨Sh, hSh1, hSh2⟩ := GlobalTheory.RunIn.exists_short_family_small hCI D T h hGam large₂ j hj w hRw hL2 hrw hlw hSh (hA j hj w.n) hsp
    have hsize : 1 ≤ w.size := WeightFamilies.Wt.one_le_size w
    have key := GlobalTheory.T.shortGenerators_scaled_thetaLattice D _ _ j (recPJ h j hj) w s Sh c (400 * Zb D large₂ * w.size) hs hc0
      (mul_nonneg (by linarith) (by linarith)) hsc hSh1 hSh2
    have hG := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j w p hL2 hn8).2.1
    unfold ShortG at key ⊢
    obtain ⟨S', hS'1, hS'2, hS'3⟩ := key
    exact ⟨S', hS'1, hS'2, fun g hg => (hS'3 g hg).trans (by nlinarith)⟩
  unfold ScalB
  refine ⟨hWeq ▸ hsW.1, hsz.1, hsz.2.1, hsz.2.2.1, fun σ => ?_, p, (Formalism.MainNotions.Gaps.FamilyHypotheses.ownPr_iff D p).1 hp,
    fun σ => hsz.2.2.2 σ, 1009 * Zb D large₂, le_rfl, ?_⟩
  · rw [hWeq]
    exact ⟨(hsW.2 σ).1, (hsW.2 σ).2.1⟩
  unfold S4
  have hsizeL : 1 ≤ wL.size := WeightFamilies.Wt.one_le_size wL
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨hRL, hrL, hlL⟩ := hW wL (by simp)
    have hnL : 0 < wL.n := by omega
    obtain ⟨N, w0, hspan, -, hsup⟩ := GlobalTheory.T.exists_short_finite_generators_thetaLattice hCI D T h hGam large₂ j hj wL hRL hL2 hrL hlL
    have hG := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j wL p hL2 hnL).2.2
    have hdisc : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| := by
      rw [Real.log_abs]
      exact Real.log_intCast_nonneg _
    have hb : 0 ≤ 400 * Zb D large₂ * wL.size + 3 * D.R.f * D.R.r * wL.n * large₂.sc.L +
        5 * Real.log (Module.finrank ℚ (recB h.toLawsCore).KO) +
        Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| / Module.finrank ℚ (recB h.toLawsCore).KO + 2 := by
      have h1 : 0 ≤ Real.log (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) := Real.log_natCast_nonneg _
      have h2 : 0 ≤ (3 * D.R.f * D.R.r * wL.n : ℝ) * large₂.sc.L := mul_nonneg (by positivity) (by linarith)
      have h3 : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| / Module.finrank ℚ (recB h.toLawsCore).KO :=
        div_nonneg hdisc (by positivity)
      have h4 : 0 ≤ 400 * Zb D large₂ * wL.size := mul_nonneg (by linarith) (by linarith)
      linarith
    exact (GlobalTheory.ScaledGenerators.scaled_family D _ _ j (recPJ h j hj) ka wL wF _ N w0 _ _ _ 0
      (mul_nonneg (by linarith) (by linarith)) hb (fun σ => (hsz.2.2.2 σ).1) hspan hsup hG).1
  · have hsF : ∀ σ : (recB h.toLawsCore).KO →+* ℂ, Real.log ‖σ ((scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn).sF : (recB h.toLawsCore).KO)‖ ≤ (lamStar D + 2 * Real.log p) * wF.size :=
      fun σ => (hsz.2.2.2 σ).2.1
    exact hShort wF _ _ (by simp) hSpF hsz.1 (mul_nonneg (by linarith) (by linarith [WeightFamilies.Wt.one_le_size wF])) (by nlinarith [WeightFamilies.Wt.one_le_size wF]) hsF
  · exact hShort _ _ _ (by simp) hSpF0 hsz.2.1 (mul_nonneg (by linarith) (by linarith [WeightFamilies.Wt.one_le_size ((recPJ h j hj).wF0 wL wF)])) le_rfl (fun σ => (hsz.2.2.2 σ).2.2.1)
  · exact hShort ka _ _ (by simp) hSpK hsz.2.2.1 (mul_nonneg (by linarith) (by linarith [WeightFamilies.Wt.one_le_size ka])) le_rfl (fun σ => (hsz.2.2.2 σ).2.2.2)

end GlobalTheory.RunIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunScalarsNonzeroBoundedSupBoundStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.runScalars_nonzero_bounded_supBound : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → LawsSh T → (∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1) → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.OwnPr D p → FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) wF → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ((recPJ h j hj).wF0 wL wF) → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) ka → ScalB large₂ (recPJ h j hj) H.C1 H.A1 (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn := by
  first | exact @GlobalTheory.RunIn.scalB_rec | exact GlobalTheory.RunIn.scalB_rec | (intros; apply GlobalTheory.RunIn.scalB_rec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsRunDataGeneratingScaledThetaLatticeWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsRunDataGeneratingScaledThetaLatticeWeight
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem exists_tiedW_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (Gc Prw : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ThInt (recPJ h j hj) hinj EX wL → EtaleWeightGaps.GrowthConstantBound large₂ (recB h.toLawsCore) Gc → 38 * large₂.sc.L + PO D large₂ ≤ Prw → ∃ G : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF, G.TiedW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) Gc Prw := by
  intro hC D T h hG hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw hP hR hI hG4 hPrw
  obtain ⟨hL, hf, hr, hlam, -, -⟩ := GlobalTheory.page_two_le_L_and_signs D _ _ j _ large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hR
  obtain ⟨hDF, hn, hrn, hLP⟩ :=
    (GlobalTheory.RunWeights.weights_below D _ _ j _ large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj.1 hP).1 wL (by simp)
  have hL0 : 0 ≤ large₂.sc.L := by linarith
  have hRL := GlobalTheory.pageRows_of_le D large₂ j ka wL hL0 hDF hn hR
  have hn0 : 0 < wL.n := by omega
  have hO : OPO large₂ (recB h.toLawsCore) := by
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, -⟩, -⟩ := hP
    exact hO
  obtain ⟨N, w0, hspan, hN, hsup⟩ := GlobalTheory.T.exists_short_finite_generators_thetaLattice hC D T h hG large₂ j hj wL hRL hL hrn hLP
  have hcount := log_count_le_mul_size D _ large₂ j wL N Prw hL hn0 hRL hO hPrw hN
  have hs : (0 : ℝ) ≤ wL.size := by
    have h1 := frn_le_size_sub_one wL
    have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * wL.n := by positivity
    push_cast at h1
    linarith
  have hp : 0 ≤ Real.log (D.host.pde : ℝ) := Real.log_natCast_nonneg _
  have hZ : 0 ≤ Zb D large₂ := by unfold Zb; positivity
  have hnum := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j wL D.host.pde hL hn0).2.2
  have hGc := mul_le_mul_of_nonneg_right (hG4 D.host.pde (by simp)) hs
  have hd : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| := by
    rw [Real.log_abs]; exact Real.log_intCast_nonneg _
  have hK : 0 ≤ Real.log (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) := Real.log_natCast_nonneg _
  refine (GlobalTheory.ScaledGenerators.scaled_family D _ _ j (recPJ h j hj) ka wL wF (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) N w0
    ((lamStar D + 2 * Real.log D.host.pde) * wL.size) _ Gc Prw (by positivity) (by positivity) (fun σ => ?_)
    hspan hsup (hnum.trans hGc)).2 hI hcount
  rw [sW_eq_sOf]
  refine ((GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D _ hinj EX j wL).2 σ).2.2.2.trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hs

end GlobalTheory.RunIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsRunDataGeneratingScaledThetaLatticeWeightStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_runData_generating_scaled_thetaLattice_weight : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (Gc Prw : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ThInt (recPJ h j hj) hinj EX wL → EtaleWeightGaps.GrowthConstantBound large₂ (recB h.toLawsCore) Gc → 38 * large₂.sc.L + PO D large₂ ≤ Prw → ∃ G : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF, G.TiedW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) Gc Prw := by
  first | exact @GlobalTheory.RunIn.exists_tiedW_rec | exact GlobalTheory.RunIn.exists_tiedW_rec | (intros; apply GlobalTheory.RunIn.exists_tiedW_rec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortSpanThetaTieOfScalars
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem exists_short_span_thetaTie_of_scalars : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (C1 A1 Gc : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ), ScalB large₂ X C1 A1 S ka wL wF Tn → EtaleWeightGaps.GrowthConstantBound large₂ B Gc → ∃ Sh : Finset (B.Cusp j wF), Submodule.span B.KO (Sh : Set (B.Cusp j wF)) = ⊤ ∧ (∀ g ∈ Sh, g ∈ X.Thc S.sF wF ∧ WeightFamilies.meanLogSup B g ≤ Gc * wF.size) ∧ ∀ G : EtaleWeightGaps.GlobalFamilyData X ka wL wF, (∀ i, G.th' i ∈ Sh) → G.TiedTh S Gc := by
  intro D B P j X large₂ C1 A1 Gc S ka wL wF Tn hS hG
  obtain ⟨-, -, -, -, -, po, hpo, -, PLam, hPLam, -, ⟨Sh, hSub, hSpan, hMean⟩, -, -⟩ := hS

  have hconst : Formalism.MainNotions.WeightAlgebra.Gc large₂ B PLam po ≤ Gc := by
    refine le_trans ?_ (hG po hpo)
    unfold Formalism.MainNotions.WeightAlgebra.Gc
    linarith
  have hbound : Formalism.MainNotions.WeightAlgebra.Gc large₂ B PLam po * wF.size ≤ Gc * wF.size :=
    mul_le_mul_of_nonneg_right hconst (le_trans zero_le_one wF.one_le_size)
  refine ⟨Sh, hSpan, fun g hg => ⟨hSub hg, (hMean g hg).trans hbound⟩, fun G hG' i => ?_⟩
  exact ⟨hSub (hG' i), (hMean _ (hG' i)).trans hbound⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunHypothesesFormsScalarsOfParameterConditions
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunJoin

theorem log_DF_le_of_rows {D : D7} {j : ℕ} (large₂ : SizeData₂ D) (ka w : WeightFamilies.Wt D j) (h3 : 3 ≤ DF w) (hle : DF w ≤ DF ka)
    (hrow : Real.log (1 + DF ka) ≤ 2 * large₂.sc.L) : Real.log (DF w) ≤ 2 * large₂.sc.L := by
  have hpos : (0 : ℝ) < (DF w : ℝ) := by
    have h0 : 0 < DF w := by omega
    exact_mod_cast h0
  have hmono : (DF w : ℝ) ≤ 1 + (DF ka : ℝ) := by
    have h1 : (DF w : ℝ) ≤ (DF ka : ℝ) := by exact_mod_cast hle
    linarith
  exact (Real.log_le_log hpos hmono).trans hrow


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem hypC_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0 (nusR h j wL) ∧ LatAt (recB h.toLawsCore) j ka ∧ (∀ w : WeightFamilies.Wt D j, GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w) ∧ PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) wL ∧ ∃ Sh : Finset ((recB h.toLawsCore).Cusp j wF), Submodule.span (recB h.toLawsCore).KO (Sh : Set ((recB h.toLawsCore).Cusp j wF)) = ⊤ ∧ ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, (∀ i, G.th' i ∈ Sh) → G.TiedTh (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) (gcR large₂ (recB h.toLawsCore)) := by
  intro D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hpar hpage
  have hj1 : 1 ≤ j := hj.1
  have hjm : j ≤ D.R.m := hj.2
  obtain ⟨hParA, hSetC, -, -, -⟩ := hpage.hyp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hnW, -, hIsL, hIsF, -⟩ := hSetC
  have hchart := GlobalTheory.T.harmonic_germ_value_chart_independent
  have hgam : GlobalTheory.RunIn.GamAt T.toCore := GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore
  have hrows := (GlobalTheory.pageRows_of_pageAt D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hpage.hyp hpage.page hpage.ck).1
  have hwb := GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hj1 hpage.hyp
  have hLle : DF wL ≤ DF ka := (hwb.1 wL (by simp)).1
  have hlogL : Real.log (DF wL) ≤ 2 * large₂.sc.L :=
    log_DF_le_of_rows large₂ ka wL hpage.df hLle hrows.2.2.2.2.2.2.2.1
  have hn : 2 * D.R.f * D.R.r ≤ wL.n := by
    rw [hIsL.1]
    have hr : 2 ≤ D.R.r + 1 := by have := hpage.r8; omega
    calc 2 * D.R.f * D.R.r = D.R.f * D.R.r * 2 := by ring
      _ ≤ D.R.f * D.R.r * (D.R.r + 1) := Nat.mul_le_mul_left _ hr
      _ ≤ nW := hnW
  have hH1 := (GlobalTheory.DepthSum.depth_sum_record D T h j hj large₂ wL hn hlogL).1
  have hown : FamilyHypotheses.OwnPr D p := by
    obtain ⟨q, hq, hall⟩ := hpar.sh.dPd
    have e : p = q := (hpar.own 0).symm.trans (hall j hj 0)
    subst e
    exact hq
  have hH2 := (GlobalTheory.T.scaledRunLattices_in_supLattices D T h hpar.sh j hj hinj EX hpar.orient p hpar.own ka wL wF Tn nP hIsF).1
  have hth : ∀ w : WeightFamilies.Wt D j, GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w :=
    fun w => GlobalTheory.T.scaledThetaLattice_le_supLattice_every_weight D T h j hj hinj EX hpar.orient w
  have helper : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GlobalTheory.RunIn.GamAt T.toCore → LawsSh T → 0 < badN D → (∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1) → (∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0) → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (Gc Prw : ℝ), FamilyHypotheses.OwnPr D p → FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → PageAt large₂ C2 A2 → 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f → (∀ w2, IsG2 wL wF w2 → GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w2) → (j < D.R.m → ∀ w1, IsDoubledWeightWithShift wL w1 nW → GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w1) → H2 (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF → EtaleWeightGaps.GrowthConstantBound large₂ (recB h.toLawsCore) Gc → 38 * large₂.sc.L + PO D large₂ ≤ Prw → (∀ nus, EtaleWeightGaps.WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → EtaleWeightGaps.HypC large₂ (recPJ h j hj) H C2 A2 CR 0 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0 nus) ∧ ∃ (G₀ : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF) (Sh : Finset ((recB h.toLawsCore).Cusp j wF)), Submodule.span (recB h.toLawsCore).KO (Sh : Set ((recB h.toLawsCore).Cusp j wF)) = ⊤ ∧ G₀.TiedW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) Gc Prw ∧ NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G₀.w i).1) ∧ ∀ G : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF, (∀ i, G.th' i ∈ Sh) → G.TiedTh (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) Gc := by
    suffices hInputs : _ by exact hInputs
    intro hCI D T h hGam hSh hbad hA1 hUX hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw
      hOwn hHP hPA hCK hThG2 hThG1 hH2 hG4 hPrw
  
    obtain ⟨hRows, h16⟩ := GlobalTheory.T.sizePageRows_of_sizePageAt D (recB h.toLawsCore) T.G.P j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP
      nW h0 hHP hPA hCK
  
    obtain ⟨hW, hWn, -, -⟩ := GlobalTheory.RunWeights.weights_below D (recB h.toLawsCore) T.G.P j (recPJ h j hj) large₂ H C2 A2 CR CT
      ka wL wF Tn nP nW h0 hj.1 hHP
  
    have hSpan : ∀ w, w ∈ ({wL, wF, (recPJ h j hj).wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)) →
        8 * D.R.f * D.R.r + 4 ≤ w.n → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) w := fun w hw hn =>
      GlobalTheory.T.shortThetaSeries_span_cuspForms_weight hCI D T h hSh hGam hbad hUX j hj.1 hj.2 w
        (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w (hW w hw).2.2.2) hn
    have hSB := GlobalTheory.T.runScalars_nonzero_bounded_supBound hCI D T h hGam hSh hA1 hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hOwn hHP hRows
      (hSpan wF (by simp) (hWn wF (by simp))) (hSpan _ (by simp) (hWn _ (by simp))) (hSpan ka (by simp) (hWn ka (by simp)))
    have hI4 := GlobalTheory.T.exists_integral_auxiliary_cuspForms_supBound hCI D T h hGam hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hHP hRows h16 hThG2 hThG1
  
    have hThL : GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX wL := by
      have hW0 := hH2.1
      rw [GlobalTheory.RunIn.sW_eq_sOf] at hW0
      exact hW0
    obtain ⟨G₀, hG₀⟩ := GlobalTheory.T.exists_runData_generating_scaled_thetaLattice_weight hCI D T h hGam hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw hHP hRows
      hThL hG4 hPrw
    obtain ⟨Sh, hSh', -, hTh⟩ := GlobalTheory.exists_short_span_thetaTie_of_scalars D (recB h.toLawsCore) T.G.P j (recPJ h j hj) large₂
      H.C1 H.A1 Gc (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn hSB hG4
    have hsW : (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn).sW ≠ 0 := by
      rw [GlobalTheory.RunIn.sW_eq_sOf]
      exact (GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D (recB h.toLawsCore) hinj EX j wL).1
    refine ⟨fun nus hnus => (FamilyHypotheses.hypC_iff large₂ (recPJ h j hj) H C2 A2 CR CT _ ka wL wF Tn nP nW h0 nus).2
        ⟨hHP, hSB, hnus, hH2, hI4⟩, G₀, Sh, hSh', hG₀, ?_, hTh⟩
    exact GlobalTheory.T.scaledThetaLattice_generators_noCommonZero hCI D T h EX j hj _ large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw hHP hsW G₀ hG₀
  have main := helper hchart D T h hgam hpar.sh hpar.bad hpar.lvA hpar.same hinj EX p j hj large₂ H C2 A2 7 CT
    ka wL wF Tn nP nW h0 (gcR large₂ (recB h.toLawsCore)) (38 * large₂.sc.L + PO D large₂) hown hpage.hyp hpage.page hpage.ck
    (fun w2 _ => hth w2) (fun _ w1 _ => hth w1) hH2 (growthConstantBound_gcR large₂ _) le_rfl
  have hC := main.1 _ hH1
  obtain ⟨-, Sh, hspan, -, -, hTied⟩ := main.2
  have hsK := hC.2.2.1.2.2.2.1
  have hspanka := GlobalTheory.T.shortThetaSeries_span_cuspForms_weight hchart D T h hpar.sh hgam hpar.bad hpar.same j hj1 hjm ka
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj ka (hwb.1 ka (by simp)).2.2.2) (hwb.2.1 ka (by simp))
  have hlat := GlobalTheory.T.weightModule_isLattice_of_shortSeries_span D T.toCore h.toLawsCore hgam large₂ H.CA hParA j ka _ (recPJ h j hj) _ wL wF hsK hspanka
    hC.2.2.2.2.1
  refine ⟨hC, hlat, hth, ⟨hpage.p13, fun σ => ?_, hpage.frd, hpage.r8, hpage.df⟩, Sh, hspan, hTied⟩
  rw [GlobalTheory.RunIn.sW_eq_sOf]
  exact ((GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D _ hinj EX j wL).2 σ).2.2.1

end GlobalTheory.RunJoin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunHypothesesFormsScalarsOfParameterConditionsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.runHypotheses_formsScalars_of_parameterConditions : ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), ParOK T EX p j → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0 (nusR h j wL) ∧ LatAt (recB h.toLawsCore) j ka ∧ (∀ w : WeightFamilies.Wt D j, GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w) ∧ PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) wL ∧ ∃ Sh : Finset ((recB h.toLawsCore).Cusp j wF), Submodule.span (recB h.toLawsCore).KO (Sh : Set ((recB h.toLawsCore).Cusp j wF)) = ⊤ ∧ ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, (∀ i, G.th' i ∈ Sh) → G.TiedTh (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) (gcR large₂ (recB h.toLawsCore)) := by
  exact @GlobalTheory.RunJoin.hypC_record
end
