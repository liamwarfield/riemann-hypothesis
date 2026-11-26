module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ScaledThetaLatticeGeneratorsNoCommonZero
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBlockProductMemIntegralHarmonic
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledThetaLatticeLeSupLatticeEveryWeight
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortThetaFamilyWithBlockPolynomialRules
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortThetaFamilyWithBlockPolynomialRules
noncomputable section

namespace GlobalTheory.BlockTh

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem span_sum_elim {R M ι κ : Type} [CommRing R] [AddCommGroup M] [Module R M] (S : Submodule R M) (u : ι → M)
    (v : κ → M) (hu : Submodule.span R (Set.range u) = S) (hv : ∀ k, v k ∈ S) :
    Submodule.span R (Set.range (Sum.elim u v)) = S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i | k, rfl⟩
    · rw [← hu]
      exact Submodule.subset_span ⟨i, rfl⟩
    · exact hv k
  · rw [← hu]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i, rfl⟩

private theorem span_range_sum_elim_eq_thAll {D : D7} {Pr : ModuliIntegralCharts.Prov D} {j : ℕ} (B : WeightFamilies.Prov D) (X : PJ D B Pr j)
    (w : WeightFamilies.Wt D j) {N M' : ℕ} {ι : Type} (w0 : Fin N → B.Cusp j w) (v : ι → B.Cusp j w) (e : Fin M' ≃ Fin N ⊕ ι)
    (h0 : Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll w) (hv : ∀ q, v q ∈ X.thAll w) :
    Submodule.span (𝓞 B.KO) (Set.range (fun k => Sum.elim w0 v (e k))) = X.thAll w := by
  rw [show Set.range (fun k => Sum.elim w0 v (e k)) = Set.range (Sum.elim w0 v) from
    EquivLike.range_comp (Sum.elim w0 v) e]
  exact span_sum_elim _ w0 v h0 hv

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem theta_family_block : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → D.R.f * D.R.r * (D.R.r + 1) ≤ 2 * w.n → ∃ (N : ℕ) (w0 : Fin N → (recB h.toLawsCore).Cusp j w) (P₁ : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA w) w.n ∧ GlobalTheory.BlockTh.IsBlockProd P₁ ∧ ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) 1 P₁ (fun k => ((w0 k).1 : T.R j)) ∧ (fun (B : WeightFamilies.Prov D) (X : PJ D B T.G.P j) (w1 : Fin N → B.Cusp j w) => Submodule.span (𝓞 B.KO) (Set.range w1) = X.thAll w) (recB h.toLawsCore) (recPJ h j hj) w0 ∧ N ≤ 2 * ((D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ (recB h.toLawsCore).KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n))) ∧ ∀ k σ, Real.log ((recB h.toLawsCore).supN j w σ (w0 k)) ≤ 400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ (recB h.toLawsCore).KO) + Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| / Module.finrank ℚ (recB h.toLawsCore).KO + 2 := by
  intro hC D T h hG large₂ j hj w hP hL hr hlast hn
  obtain ⟨N0, w0, hspan, hN0, hsup0⟩ := GlobalTheory.T.exists_short_finite_generators_thetaLattice hC D T h hG large₂ j hj w hP hL hr hlast
  obtain ⟨-, ⟨hM, -⟩, -, hdat⟩ := h.toLawsCore.pins
  obtain ⟨hp, hq, -⟩ := hdat j hj
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hp, hq]
    exact Formalism.L2.Geo.sigW_sum D hj.1 hj.2
  have hfE : I2.PT.f D.host.E = D.R.f := by
    dsimp only [I2.PT.f]
    rw [Formalism.MainNotions.StandardLattice.finrank_host D]
    omega
  have he : ∀ {m : ℕ} (g : Fin m → ℕ), Antitone g → ∀ i k : ℕ, i ≤ k → ext0 g k ≤ ext0 g i := by
    intro m g hg i k hik
    dsimp only [ext0]
    by_cases h1 : k < m <;> by_cases h2 : i < m
    · rw [dite_eq_left h1, dite_eq_left h2]
      exact hg (Fin.mk_le_mk.2 hik)
    · exact absurd (lt_of_le_of_lt hik h1) h2
    · rw [dite_eq_right h1]
      exact Nat.zero_le _
    · rw [dite_eq_right h1, dite_eq_right h2]
  have hanti : ∀ τ i k, i ≤ k → wtA w (τ, k) ≤ wtA w (τ, i) := by
    intro τ i k hik
    dsimp only [wtA]
    apply Finset.sum_le_sum
    intro t _
    apply add_le_add
    · split_ifs
      · exact he _ (w.aPlus_antitone t) i k hik
      · exact le_rfl
    · split_ifs
      · exact he _ (w.aM_anti t) i k hik
      · exact le_rfl
  obtain ⟨P, hPh, hPb, hPdeg, hPl1⟩ := GlobalTheory.T.exists_blockProduct_mem_integralHarmonic D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c (wtA w) w.n hanti
    (by rw [hfE, hpq]; exact hn)
  have hdom : Dom (wtA w) w.n := dom_wtA w
  have hlp : LastPos (T.Q.Dw j) (wtA w) := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hlast
  obtain ⟨_, hnab⟩ := h.nabPin j hj
  have hex : ∀ q : Fin w.n → LevQ (T.Q.Dw j) T.Q.l, ∃ f : T.R j,
      IsThRule (T.Q.Xo j) T.Q.c (T.nab j) (fun b => levRep (q b)) P f :=
    fun q => by
      obtain ⟨⟨f, hf, -⟩, -⟩ := GlobalTheory.thetaRule_exists_and_eval hC D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
        (T.nab j) hnab (wtA w) w.n (fun b => levRep (q b)) P hPh
      exact ⟨f, hf⟩
  choose f hf using hex
  have hfC : ∀ q, f q ∈ cutR T.C j w := by
    intro q
    have h1 : f q ∈ T.C j w := h.thCusp j hj (wtA w) w.n hdom hlp (f q) ⟨fun b => levRep (q b), P, hPh, hf q⟩
    dsimp only [cutR]
    exact Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun hn' => absurd hj hn'⟩
  let v : (Fin w.n → LevQ (T.Q.Dw j) T.Q.l) → (recB h.toLawsCore).Cusp j w := fun q =>
    (⟨f q, hfC q⟩ : cutR T.C j w)
  have hv1 : ∀ q, ((v q : cutR T.C j w) : T.R j) = f q := fun q => rfl
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.card_lattice_quotient_half_level D.host.E T.Q.H (T.Q.Dw j) T.Q.l
  let _ : Fintype (LevQ (T.Q.Dw j) T.Q.l) := Fintype.ofFinite _
  let e : Fin (N0 + Fintype.card (Fin w.n → LevQ (T.Q.Dw j) T.Q.l)) ≃ Fin N0 ⊕ (Fin w.n → LevQ (T.Q.Dw j) T.Q.l) :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin _).symm)
  let W : Fin (N0 + Fintype.card (Fin w.n → LevQ (T.Q.Dw j) T.Q.l)) → (recB h.toLawsCore).Cusp j w :=
    fun k => Sum.elim w0 v (e k)
  have hWq : ∀ q, W (e.symm (Sum.inr q)) = v q := by
    intro q
    simp only [W, Equiv.apply_symm_apply, Sum.elim_inr]
  refine ⟨_, W, P, hPh, hPb, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun q => e.symm (Sum.inr q), fun a b hab => Sum.inr_injective (e.symm.injective hab), fun q => ⟨f q, hf q, fun p y => ?_⟩⟩
    show (W (e.symm (Sum.inr q))).1 p y = _
    rw [hWq q, map_one, one_mul]
  · refine span_range_sum_elim_eq_thAll (recB h.toLawsCore) (recPJ h j hj) w w0 v e hspan fun q => ?_
    dsimp only [recPJ, mkX, spanIn]
    simp only [Submodule.mem_comap]
    exact Submodule.subset_span (show f q ∈ T.th j w from ⟨fun b => levRep (q b), P, hPh, hf q⟩)
  · have hfd : FD.fdeg D.host.E = D.R.f := by
      dsimp only [FD.fdeg]
      rw [Formalism.MainNotions.StandardLattice.finrank_host D]
      omega
    have hc : Fintype.card (Fin w.n → LevQ (T.Q.Dw j) T.Q.l) =
        (D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) := by
      rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard, hM, hpq, hfd, ← pow_mul]
    have hB1 : 0 < Module.finrank ℚ (recB h.toLawsCore).KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n) :=
      Nat.mul_pos Module.finrank_pos (pow_pos (by omega) _)
    have hGX := Nat.le_mul_of_pos_right ((D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n)) hB1
    rw [hc]
    linarith
  · intro k σ
    obtain ⟨x, rfl⟩ : ∃ x, e.symm x = k := ⟨e k, e.symm_apply_apply k⟩
    rcases x with i | q
    · have h0 : W (e.symm (Sum.inl i)) = w0 i := by
        simp only [W, Equiv.apply_symm_apply, Sum.elim_inl]
      rw [h0]
      exact hsup0 i σ
    · rw [hWq q]
      have hs : (recB h.toLawsCore).supN j w σ (v q) = T.Ns j w σ (f q) := by
        change cutN T.C T.Ns j w σ (v q) = _
        dsimp only [cutN]
        rw [if_pos hj]
      rw [hs]
      have h2 : ((Formalism.MainNotions.WeightAlgebra.DF w : ℕ) : ℝ) = Formalism.MainNotions.WeightAlgebra.absA w := by
        dsimp only [Formalism.MainNotions.WeightAlgebra.DF, Formalism.MainNotions.WeightAlgebra.degP, Formalism.MainNotions.WeightAlgebra.absA]
        push_cast
        rfl
      have hDF : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ Formalism.MainNotions.WeightAlgebra.absA w := by
        rw [← h2]
        exact_mod_cast ReciprocityTheory.ChartRestriction.G.PullbackSections.DF_wtA_le T j w
      have hA0 : 0 ≤ Formalism.MainNotions.WeightAlgebra.absA w := by
        rw [← h2]
        positivity
      rw [hpq] at hPl1
      have hℓ0 : 0 ≤ Real.log (max 1 ((D.R.r : ℝ) ^ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w))) :=
        Real.log_nonneg (le_max_left _ _)
      have hℓexp : l1At σ P ≤ Real.exp (Real.log (max 1 ((D.R.r : ℝ) ^ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w)))) := by
        rw [Real.exp_log (lt_of_lt_of_le one_pos (le_max_left _ _))]
        dsimp only [l1At]
        exact le_trans (hPl1 σ) (le_max_right _ _)
      have hℓle : Real.log (max 1 ((D.R.r : ℝ) ^ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w))) ≤
          (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) * D.R.r := by
        rcases Nat.eq_zero_or_pos D.R.r with h0 | h0
        · rw [h0, Nat.cast_zero, mul_zero, max_eq_left (pow_le_one₀ le_rfl zero_le_one), Real.log_one]
        · have h1 : (1 : ℝ) ≤ (D.R.r : ℝ) ^ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) := one_le_pow₀ (by exact_mod_cast h0)
          rw [max_eq_right h1, Real.log_pow]
          exact mul_le_mul_of_nonneg_left (Real.log_le_self (by positivity)) (by positivity)
      have hNs := GlobalTheory.T.log_supNorm_thetaGenerator_le hC D T h hG large₂ j hj w hP hL hr hlp (fun b => levRep (q b)) P hPh (f q) (hf q) σ _ hℓ0 hℓexp
      have hL0 : (0 : ℝ) ≤ large₂.sc.L := by linarith
      have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
      have t1 : 0 ≤ 3 * (D.R.f : ℝ) * D.R.r * w.n * large₂.sc.L := mul_nonneg (by positivity) hL0
      have t2 : 0 ≤ 5 * Real.log (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) :=
        mul_nonneg (by norm_num) (Real.log_nonneg (Nat.one_le_cast.2 Module.finrank_pos))
      have t3 : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| /
          (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) := by
        apply div_nonneg _ (Nat.cast_nonneg _)
        apply Real.log_nonneg
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero _)
      rcases Nat.eq_zero_or_pos w.n with hn0 | hwn
      · have hr0' : D.R.r = 0 := by omega
        have hs1 : (D.R.sigW j).1 = 0 := by omega
        have hs2 : (D.R.sigW j).2 = 0 := by omega
        have hA : Formalism.MainNotions.WeightAlgebra.absA w = 0 := by
          have : IsEmpty (Fin (D.R.sigW j).1) := by rw [hs1]; infer_instance
          have : IsEmpty (Fin (D.R.sigW j).2) := by rw [hs2]; infer_instance
          simp [Formalism.MainNotions.WeightAlgebra.absA]
        have hZ0 : Zb D large₂ = 0 := by simp [Zb, hr0']
        have hrc : (D.R.r : ℝ) = 0 := by exact_mod_cast hr0'
        rw [hA, hrc] at hNs
        rw [hrc] at hℓle
        rw [hZ0]
        nlinarith
      · have h9430 := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j w 0 hL hwn).1
        have hk1 : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) * D.R.r ≤ 140 * D.R.r * large₂.sc.L * Formalism.MainNotions.WeightAlgebra.absA w := by
          have : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) * D.R.r ≤ Formalism.MainNotions.WeightAlgebra.absA w * D.R.r :=
            mul_le_mul_of_nonneg_right hDF hr0
          nlinarith [mul_nonneg hA0 hr0]
        linarith

end GlobalTheory.BlockTh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortThetaFamilyWithBlockPolynomialRulesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_short_thetaFamily_with_block_polynomial_rules : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → D.R.f * D.R.r * (D.R.r + 1) ≤ 2 * w.n → ∃ (N : ℕ) (w0 : Fin N → (recB h.toLawsCore).Cusp j w) (P₁ : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA w) w.n ∧ GlobalTheory.BlockTh.IsBlockProd P₁ ∧ ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) 1 P₁ (fun k => ((w0 k).1 : T.R j)) ∧ (fun (B : WeightFamilies.Prov D) (X : PJ D B T.G.P j) (w1 : Fin N → B.Cusp j w) => Submodule.span (𝓞 B.KO) (Set.range w1) = X.thAll w) (recB h.toLawsCore) (recPJ h j hj) w0 ∧ N ≤ 2 * ((D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ (recB h.toLawsCore).KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n))) ∧ ∀ k σ, Real.log ((recB h.toLawsCore).supN j w σ (w0 k)) ≤ 400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ (recB h.toLawsCore).KO) + Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| / Module.finrank ℚ (recB h.toLawsCore).KO + 2 := by
  first | exact @GlobalTheory.BlockTh.theta_family_block | exact GlobalTheory.BlockTh.theta_family_block | (intros; apply GlobalTheory.BlockTh.theta_family_block <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LowerBoundAtFramesFamilyWithScaledThetaRules
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LowerBoundAtFramesFamilyWithScaledThetaRules
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegreeInterpolationBounds

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem totalDegree_eq_DF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : Coeff l) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) (h0 : P ≠ 0) :
    P.totalDegree = Formalism.L2.Pj.DF Dw a := by
  have key : ∀ m ∈ P.support, (m.sum fun _ e => e) = Formalism.L2.Pj.DF Dw a := by
    intro m hm
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Formalism.L2.Pj.DF]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hP.1.2.2 m hm τ i
  obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 h0)
  apply le_antisymm
  · exact Finset.sup_le fun m' hm' => (key m' hm').le
  · exact (key m hm) ▸ MvPolynomial.le_totalDegree hm

theorem pow_le_sq_of_log {M x : ℝ} {d : ℕ} (hM : 1 < M) (hd : 1 ≤ d) (hx : 0 ≤ x)
    (h : (d : ℝ) / 2 * Real.log M ≤ Real.log x) : M ^ d ≤ x ^ 2 := by
  have hl : 0 < Real.log M := Real.log_pos hM
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hx0 : 0 < x := by
    rcases hx.eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero] at h
      nlinarith
    · exact h0
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  linarith

theorem i2iAt_record : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (_EX : ErrX D) (j : ℕ) (hj : InR D j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (S : Scal (recB h.toLawsCore)) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → EtaleWeightGaps.PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW S wL → ∀ (P₁ : MvPolynomial (LtN (T.Q.Dw j) wL.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA wL) wL.n → GlobalTheory.BlockTh.IsBlockProd P₁ → ∀ (N : ℕ) (w : Fin (N + 1) → (recB h.toLawsCore).Cusp j wL), ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) ((S.sW : (recB h.toLawsCore).KO) : T.Q.c.F) P₁ (fun k => ((w k).1 : T.R j)) → ∀ tableLineDegreeFive : ℝ, p14 D.host.E D.R.r wL.n D.R.m ≤ tableLineDegreeFive → I2AtFramePoints (T.U j) (xiR D) (fun k => ((w k).1 : T.R j)) (wtA wL, wL.n) (I2.th (E := D.host.E) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL)))) tableLineDegreeFive (WeightAlgebra.DF wL) (cc D large₂ C2 A2 CR wL) := by
  intro hCI D T h EX j hj K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hHP hTie hPage hSupp P₁ hP hB N w hC
    tableLineDegreeFive hP14
  obtain ⟨inst, hnab⟩ := h.nabPin j hj
  obtain ⟨α, hα1, hα2⟩ := GlobalTheory.RunIn.half_level_generator_norm D T h EX
  obtain ⟨hrun, hcc, -, -⟩ := GlobalTheory.T.thetaRunParameters_at_typePrimes_product D _ _ j (recPJ h j hj) K Ch Ah Cq Aq S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0
    hHP hTie hPage hSupp
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hP0 : P₁ ≠ 0 := fun e => GlobalTheory.BlockThInhab.not_isBlockProd_zero (T.Q.Dw j) wL.n T.Q.c.F (e ▸ hB)
  have hdeg : P₁.totalDegree = WeightAlgebra.DF wL :=
    (totalDegree_eq_DF T.Q.c hP hP0).trans (GlobalTheory.WeightExponents.weight_exponents D T.Q h.pins j hj wL).1
  have hq : (T.Q.Dw j).q ≤ D.R.m := by
    rw [(h.pins.2.2.2 j hj).2.1]
    exact Nat.sub_le _ _
  have hs : ∀ σ : T.Q.c.F →+* ℂ,
      (T.Q.l.M : ℝ) ^ P₁.totalDegree ≤ ‖σ ((S.sW : (recB h.toLawsCore).KO) : T.Q.c.F)‖ ^ 2 := by
    intro σ
    have h3 : (3 : ℝ) ≤ T.Q.l.M := by exact_mod_cast T.Q.l.three_le
    refine pow_le_sq_of_log (by linarith) (by rw [hdeg]; have := hSupp.2.2.2.2; omega) (norm_nonneg _) ?_
    rw [hdeg, hM, Nat.cast_mul]
    exact hSupp.2.1 σ
  have key := GlobalTheory.T.integralityBound_of_family_containing_scaled_thetaRules hCI D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (xiR D) (T.nab j) hnab
    (fun σ hσ => ⟨h.unf j hj σ hσ, h.unTest j hj σ hσ, h.xiAbs j hj σ hσ⟩) α hα1 hα2 (wtA wL) wL.n P₁ (dom_wtA wL) hP hB
    _ hs N (fun k => ((w k).1 : T.R j)) (fun k => cusp_le_sec _ _ _ _ _ (cutR_le T.C j wL (w k).2)) hC
    (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL))) D.R.m (by rw [hdeg, hM]; exact hrun) (Or.inr hq) tableLineDegreeFive
    (cc D large₂ C2 A2 CR wL) hP14 (by rw [hM]; exact hcc)
  rw [hdeg, hM] at key
  exact key

end GlobalTheory.DegreeInterpolationBounds
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LowerBoundAtFramesFamilyWithScaledThetaRulesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_bound_at_frames_family_with_scaled_thetaRules : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (_EX : ErrX D) (j : ℕ) (hj : InR D j) (K : KAdm) (Ch Ah Cq Aq : ℝ) (S : Scal (recB h.toLawsCore)) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → EtaleWeightGaps.PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW S wL → ∀ (P₁ : MvPolynomial (LtN (T.Q.Dw j) wL.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA wL) wL.n → GlobalTheory.BlockTh.IsBlockProd P₁ → ∀ (N : ℕ) (w : Fin (N + 1) → (recB h.toLawsCore).Cusp j wL), ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) ((S.sW : (recB h.toLawsCore).KO) : T.Q.c.F) P₁ (fun k => ((w k).1 : T.R j)) → ∀ tableLineDegreeFive : ℝ, p14 D.host.E D.R.r wL.n D.R.m ≤ tableLineDegreeFive → I2AtFramePoints (T.U j) (xiR D) (fun k => ((w k).1 : T.R j)) (wtA wL, wL.n) (I2.th (E := D.host.E) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + WeightAlgebra.DF wL)))) tableLineDegreeFive (WeightAlgebra.DF wL) (cc D large₂ C2 A2 CR wL) := by
  first | exact @GlobalTheory.DegreeInterpolationBounds.i2iAt_record | exact GlobalTheory.DegreeInterpolationBounds.i2iAt_record | (intros; apply GlobalTheory.DegreeInterpolationBounds.i2iAt_record <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogTwoMulCountLeMulSize
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem log_two_mul_count_le_mul_size : ∀ (D : D7) (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j) (N : ℕ) (Prw : ℝ), 2 ≤ large₂.sc.L → 0 < w.n → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → OPO large₂ B → 38 * large₂.sc.L + PO D large₂ ≤ Prw → N ≤ 2 * ((D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ B.KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n))) → Real.log N ≤ Prw * (w.size - 1) := by
  intro D B large₂ j w N Prw hL hn hrows hO hPrw hN
  obtain ⟨hg, -, -, -, -, -, -, hX, -⟩ := hrows

  set m : ℕ := D.R.f * D.R.r * w.n with hm
  have hN' : N ≤ (D.host.g 0 * D.host.g 1) ^ m * ((2 * Module.finrank ℚ B.KO) * (1 + WeightAlgebra.DF w) ^ m) := by
    calc N ≤ _ := hN
      _ = _ := by ring
  have hL0 : (0 : ℝ) ≤ large₂.sc.L := by linarith
  have hPO : 0 ≤ PO D large₂ := by unfold PO; positivity
  have hd : Real.log ((2 * Module.finrank ℚ B.KO : ℕ) : ℝ) ≤ PO D large₂ + 1 := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℚ B.KO) with h0 | hpos
    · simp [h0]; linarith
    · have hk : ((Module.finrank ℚ B.KO : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      push_cast
      rw [Real.log_mul (by norm_num) hk]
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9; linarith
      linarith [hO.1]
  have hX' : Real.log ((1 + WeightAlgebra.DF w : ℕ) : ℝ) ≤ 2 * large₂.sc.L := by
    push_cast; exact hX
  have key := log_le_of_le_pow_mul_pow (a := 9 * large₂.sc.L + 1) (c := 2 * large₂.sc.L) (P := PO D large₂ + 1)
    (by linarith) (by linarith) (by linarith) (hg 0) (hg 1) hd hX' hN'

  have hf : 0 < D.R.f := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    have h3 : D.R.f = 2 * D.R.ord := rfl
    omega
  have hr : 0 < D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    have h3 : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hms : (m : ℝ) ≤ w.size - 1 := frn_le_size_sub_one w
  have hPrw0 : 0 ≤ Prw := by linarith
  calc Real.log N ≤ (m : ℝ) * (2 * (9 * large₂.sc.L + 1) + 2 * large₂.sc.L) + (PO D large₂ + 1) := key
    _ ≤ (m : ℝ) * (38 * large₂.sc.L + PO D large₂) := by nlinarith
    _ ≤ (m : ℝ) * Prw := by gcongr
    _ ≤ Prw * (w.size - 1) := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hms hPrw0

end GlobalTheory.RunIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdmissibleThetaLatticeGenerators
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
open GlobalTheory.RunIn GlobalTheory.BlockTh

namespace GlobalTheory.RunJoin

noncomputable def scaledFamily {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j)
    (S : Scal B) {N : ℕ} (w0 : Fin N → B.Cusp j wL) (m : ℝ) : GlobalFamilyData X ka wL wF :=
  ⟨N, fun k => (S.sW : B.KO) • w0 k, 0, fun k => k.elim0, 0, fun k => k.elim0, fun k => k.elim0,
    fun k => k.elim0, 0, fun k => k.elim0, 0, 0, fun _ => m⟩

theorem tiedW_scaledFamily {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j)
    (S : Scal B) {N : ℕ} (w0 : Fin N → B.Cusp j wL) (a b G Prw : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : ∀ σ : B.KO →+* ℂ, Real.log ‖σ (S.sW : B.KO)‖ ≤ a)
    (hspan : Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll wL)
    (hw : ∀ k σ, Real.log (B.supN j wL σ (w0 k)) ≤ b) (hG : a + b ≤ G * wL.size)
    (hM : X.WWc S.sW wL ≤ B.Mlat j wL) (hN : Real.log N ≤ Prw * (wL.size - 1)) :
    (scaledFamily X ka wL wF S w0 (a + b)).TiedW S G Prw := by
  obtain ⟨hsm, -, hmean⟩ := GlobalTheory.LogSupMultiple.log_supN_bounds D B j wL
  have hspan' := GlobalTheory.ScaledGenerators.span_scaled X wL S.sW w0 hspan
  refine ⟨hspan', ?_, hN, ?_, ?_⟩
  · intro k
    apply hM
    rw [← hspan']
    exact Submodule.subset_span ⟨k, rfl⟩
  · intro σ k
    exact hsm σ (S.sW : B.KO) (w0 k) a b (by linarith) (hs σ) (hw k σ) hb ha
  · show (∑ _σ : B.KO →+* ℂ, (a + b)) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size
    rw [hmean]
    exact hG

theorem log_le_of_le_two_mul_pow {N a b d m : ℕ} (hN0 : 0 < N) (hN : N ≤ 2 * (a ^ m * (d * b ^ m))) :
    Real.log N ≤ Real.log 2 + (m : ℝ) * (Real.log a + Real.log b) + Real.log d := by
  have hR : (N : ℝ) ≤ 2 * ((a : ℝ) ^ m * ((d : ℝ) * (b : ℝ) ^ m)) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hA : (a : ℝ) ^ m ≠ 0 := by
    intro h0
    rw [h0, zero_mul, mul_zero] at hR
    linarith
  have hD : (d : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, mul_zero, mul_zero] at hR
    linarith
  have hB : (b : ℝ) ^ m ≠ 0 := by
    intro h0
    rw [h0, mul_zero, mul_zero, mul_zero] at hR
    linarith
  calc Real.log N ≤ Real.log (2 * ((a : ℝ) ^ m * ((d : ℝ) * (b : ℝ) ^ m))) := Real.log_le_log hNpos hR
    _ = Real.log 2 + ((m : ℝ) * Real.log a + (Real.log d + (m : ℝ) * Real.log b)) := by
      rw [Real.log_mul two_ne_zero (mul_ne_zero hA (mul_ne_zero hD hB)), Real.log_mul hA (mul_ne_zero hD hB),
        Real.log_mul hD hB, Real.log_pow, Real.log_pow]
    _ = Real.log 2 + (m : ℝ) * (Real.log a + Real.log b) + Real.log d := by ring

private theorem containsTh_of_eq_smul {D : D7} {T : Top D} (j : ℕ) {n N : ℕ}
    (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (s : T.Q.c.F) (u v : Fin N → T.R j)
    (huv : ∀ k p y, v k p y = algebraMap T.Q.c.F _ s * u k p y)
    (hc : ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) 1 P₁ u) : ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) s P₁ v := by
  obtain ⟨jb, hjb, hq⟩ := hc
  refine ⟨jb, hjb, fun q => ?_⟩
  obtain ⟨f, hf, hfe⟩ := hq q
  refine ⟨f, hf, fun p y => ?_⟩
  rw [huv, hfe, map_one, one_mul]


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_genOK : ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), GlobalTheory.PtTie.Oriented T EX → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → ∃ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) (cc D large₂ C2 A2 7 wL) := by
  intro D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hOr hP
  have hC := GlobalTheory.T.harmonic_germ_value_chart_independent
  have hGam : GamAt T.toCore := GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore
  obtain ⟨hrows, -⟩ := GlobalTheory.pageRows_of_pageAt D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hP.hyp hP.page hP.ck
  obtain ⟨hL, -, hr6, hlam, -, -⟩ := GlobalTheory.page_two_le_L_and_signs D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn
    nP nW h0 hP.hyp hrows
  obtain ⟨hw4, -⟩ := GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hj.1
    hP.hyp
  obtain ⟨hDF, hnk, hrn, hlast⟩ := hw4 wL (by simp)
  have hrowsL := GlobalTheory.pageRows_of_le D large₂ j ka wL (by linarith) hDF hnk hrows
  have hS := GlobalTheory.RunIn.sW_eq_sOf (recB h.toLawsCore) hinj EX p ka wL wF Tn
  have hsOf := GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D (recB h.toLawsCore) hinj EX j wL
  have hsupp : EtaleWeightGaps.PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) wL :=
    ⟨hP.p13, fun σ => by rw [hS]; exact (hsOf.2 σ).2.2.1, hP.frd, hP.r8, hP.df⟩
  obtain ⟨hC1, hA1, hCc, hAc, hCR, h12⟩ := hP.tie
  have htie : TieC (⟨0, 2, 0, 2, 0, 2, 0, 4, 7⟩ : KAdm) H 1 4 0 11 C2 A2 7 :=
    ⟨hC1, hA1, hCc, hAc, hCR, rfl, rfl, h12, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  obtain ⟨-, -, -, hfrr⟩ := GlobalTheory.T.thetaRunParameters_at_typePrimes_product D _ _ j (recPJ h j hj) _ 1 4 0 11
    (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hP.hyp htie hP.page hsupp
  obtain ⟨N, w0, P₁, hharm, hblk, hcont, hspan, hNle, hsup⟩ :=
    GlobalTheory.T.exists_short_thetaFamily_with_block_polynomial_rules hC D T h hGam large₂ j hj wL hrowsL hL hrn hlast hfrr
  have hO : OPO large₂ (recB h.toLawsCore) := by
    obtain ⟨-, hSet, -⟩ := hP.hyp
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, -⟩ := hSet
    exact hO
  have hN0 : 0 < N := by
    obtain ⟨jb, -, -⟩ := hcont
    exact Fin.pos (jb 0)
  obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN0.ne'
  have hn0 : 0 < wL.n := by omega
  have hsize : (1 : ℝ) ≤ wL.size := by
    have h1 := GlobalTheory.RunIn.frn_le_size_sub_one wL
    have h2 : (0 : ℝ) ≤ ((D.R.f * D.R.r * wL.n : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hM : (recPJ h j hj).WWc (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn).sW wL ≤
      (recB h.toLawsCore).Mlat j wL := by
    rw [hS]
    exact GlobalTheory.T.scaledThetaLattice_le_supLattice_every_weight D T h j hj hinj EX hOr wL
  have hNlog := GlobalTheory.RunIn.log_two_mul_count_le_mul_size D (recB h.toLawsCore) large₂ j wL (N' + 1)
    (38 * large₂.sc.L + PO D large₂) hL hn0 hrowsL hO le_rfl hNle
  have ha : 0 ≤ lamStar D * wL.size := mul_nonneg hlam (by linarith)
  have hs : ∀ σ : (recB h.toLawsCore).KO →+* ℂ,
      Real.log ‖σ ((scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn).sW : (recB h.toLawsCore).KO)‖ ≤
        lamStar D * wL.size := fun σ => by
    rw [hS]
    exact (hsOf.2 σ).2.2.2
  have hGc := (GlobalTheory.RunIn.sup_bounds_le_Gc D (recB h.toLawsCore) large₂ j wL D.host.pde hL hn0).2.2
  have hpde : 0 ≤ Real.log (D.host.pde : ℝ) := Real.log_natCast_nonneg _
  have hfin : 0 ≤ Real.log (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) := Real.log_natCast_nonneg _
  have hdisc : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| /
      Module.finrank ℚ (recB h.toLawsCore).KO :=
    div_nonneg (by rw [Real.log_abs]; exact Real.log_intCast_nonneg _) (Nat.cast_nonneg _)
  have hZ : 0 ≤ Zb D large₂ := by
    unfold Zb
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)
  have hGg : WeightAlgebra.Gc large₂ (recB h.toLawsCore) (1009 * Zb D large₂) D.host.pde ≤ gcR large₂ (recB h.toLawsCore) := by
    unfold gcR
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hT := tiedW_scaledFamily (recPJ h j hj) ka wL wF (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) w0
    (lamStar D * wL.size) _ (gcR large₂ (recB h.toLawsCore)) (38 * large₂.sc.L + PO D large₂) ha
    (add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hZ) (by linarith))
      (mul_nonneg (by positivity) (by linarith))) (mul_nonneg (by norm_num) hfin)) hdisc) (by norm_num))
    hs hspan hsup (by nlinarith) hM hNlog
  refine ⟨scaledFamily (recPJ h j hj) ka wL wF (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) w0 _, hT,
    Nat.succ_pos N', ?_, ?_, ?_⟩
  · show Real.log ((N' + 1 : ℕ) : ℝ) ≤ nbR large₂ wL
    have hl := log_le_of_le_two_mul_pow (Nat.succ_pos N') hNle
    unfold nbR
    push_cast at hl ⊢
    linarith [hO.1]
  · exact GlobalTheory.T.scaledThetaLattice_generators_noCommonZero hC D T h EX j hj (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) large₂ H C2 A2 7 CT ka wL wF
      Tn nP nW h0 _ _ hP.hyp (by rw [hS]; exact hsOf.1) _ hT
  · exact GlobalTheory.T.lower_bound_at_frames_family_with_scaled_thetaRules hC D T h EX j hj _ 1 4 0 11 (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) large₂ H C2 A2 7 CT
      ka wL wF Tn nP nW h0 hP.hyp htie hP.page hsupp P₁ hharm hblk N' _
      (containsTh_of_eq_smul j P₁ _ _ _ (fun k q y => by
        simp only [scaledFamily]
        try rw [Submodule.coe_smul_of_tower]
        try rw [Submodule.coe_smul]
        try rw [SetLike.val_smul]
        simp only [Pi.smul_apply]
        exact Algebra.smul_def _ _) hcont) (p14R wL) (le_max_right _ _)

end GlobalTheory.RunJoin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdmissibleThetaLatticeGeneratorsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_thetaLatticeGenerators : ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), GlobalTheory.PtTie.Oriented T EX → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → ∃ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) (cc D large₂ C2 A2 7 wL) := by
  first | exact @GlobalTheory.RunJoin.exists_genOK | exact GlobalTheory.RunJoin.exists_genOK | (intros; apply GlobalTheory.RunJoin.exists_genOK <;> assumption)
end
