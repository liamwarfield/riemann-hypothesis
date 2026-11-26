module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesIsAutomorphic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesSummableMajorant
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesSummableMajorant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory

theorem poincare_sum_bound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (c : GA D V), ∃ (C₀ : ℝ) (A : ℕ), ∀ (u : GA D V → ℝ) (C : ℝ), (∀ x, 0 ≤ u x) → (∀ x, Lev.finE V x ∉ congLev D.sp.cm V.gram Λ 𝔪 → u x = 0) → (∀ x, u x ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) → ∀ g : GA D V, Summable (fun γ : GQ V => u (c * (γ : GA D V) * g)) ∧ ∑' γ : GQ V, u (c * (γ : GA D V) * g) ≤ C * C₀ * height V g ^ A := by
  intro D θ hθ V Λ hΛ 𝔪 c
  obtain ⟨C₀, A, hC⟩ := GlobalTheory.T.poincareSeries_unitary_absolutelyConvergent_moderateGrowth D θ hθ V Λ hΛ c
  refine ⟨C₀, A, fun u C hu hsupp hle g => ?_⟩
  have hP : ∀ x : GA D V, 0 < ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := fun x =>
    Finset.prod_pos fun τ _ => inv_pos.2 (pow_pos (add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg _)) _)
  have hC0 : 0 ≤ C := by
    by_contra h
    push_neg at h
    have := hle 1
    have := hu 1
    have := mul_neg_of_neg_of_pos h (hP 1)
    linarith
  have hs : ∀ s : Finset (GQ V), ∑ γ ∈ s, u (c * (γ : GA D V) * g) ≤ C * C₀ * height V g ^ A := by
    intro s
    classical
    set t := s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * g) ∈ congLev D.sp.cm V.gram Λ 𝔪) with ht
    have h1 : ∑ γ ∈ s, u (c * (γ : GA D V) * g) = ∑ γ ∈ t, u (c * (γ : GA D V) * g) := by
      rw [ht, Finset.sum_filter]
      refine Finset.sum_congr rfl fun γ _ => ?_
      split_ifs with h
      · rfl
      · exact hsupp _ h
    have h2 : ∑ γ ∈ t, u (c * (γ : GA D V) * g) ≤
        C * ∑ γ ∈ t, ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * g))) ^ (2 * V.rank ^ 2 + 1))⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun γ _ => hle _
    have h3 := hC g t (fun γ hγ => congLev_mono le_top (Finset.mem_filter.1 hγ).2)
    rw [h1, mul_assoc]
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hC0)
  have hsum : Summable (fun γ : GQ V => u (c * (γ : GA D V) * g)) :=
    summable_of_sum_le (fun γ => hu _) hs
  exact ⟨hsum, hsum.tsum_le_of_sum_le hs⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesSummableMajorantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientPoincareSeries_summable_majorant : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (c : GA D V), ∃ (C₀ : ℝ) (A : ℕ), ∀ (u : GA D V → ℝ) (C : ℝ), (∀ x, 0 ≤ u x) → (∀ x, Lev.finE V x ∉ congLev D.sp.cm V.gram Λ 𝔪 → u x = 0) → (∀ x, u x ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) → ∀ g : GA D V, Summable (fun γ : GQ V => u (c * (γ : GA D V) * g)) ∧ ∑' γ : GQ V, u (c * (γ : GA D V) * g) ≤ C * C₀ * height V g ^ A := by
  first | exact @GlobalTheory.poincare_sum_bound | exact GlobalTheory.poincare_sum_bound | (intros; apply GlobalTheory.poincare_sum_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLevelIndicatorCoefficientTestLeDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLevelIndicatorCoefficientTestLeDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.PoinTerm

theorem norm_coef_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ), KDecay M v → ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : GA D V, ‖coef θ M K v b x‖ ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := by
  intro D θ hθ V S M K v hv b hb
  choose C hC using fun τ => (hv τ).2 (b τ) (hb τ)
  have hpos : ∀ (τ : D.what₂.Tau) (x : GA D V), 0 < (1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1) := fun τ x =>
    pow_pos (add_pos_of_pos_of_nonneg one_pos (Real.sqrt_nonneg _)) _
  have hle : ∀ (τ : D.what₂.Tau) (x : GA D V), ‖⟪v τ, M.rep τ (cmp θ τ x) (b τ)⟫_ℂ‖ * (1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1) ≤ C τ :=
    fun τ x => hC τ _ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ)
  have h0 : ∀ τ, 0 ≤ C τ := fun τ => (mul_nonneg (norm_nonneg _) (hpos τ 1).le).trans (hle τ 1)
  have hP : 0 ≤ ∏ τ, C τ := Finset.prod_nonneg fun τ _ => h0 τ
  refine ⟨∏ τ, C τ, hP, fun x => ?_⟩
  unfold coef
  split_ifs
  · unfold coefR
    rw [norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun τ _ => norm_nonneg _) fun τ _ => ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (hpos τ x)]
    exact hle τ x
  · rw [norm_zero]
    exact mul_nonneg hP (Finset.prod_nonneg fun τ _ => (inv_pos.2 (hpos τ x)).le)

end GlobalTheory.PoinTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLevelIndicatorCoefficientTestLeDecayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_levelIndicatorCoefficientTest_le_decay : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ), KDecay M v → ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : GA D V, ‖coef θ M K v b x‖ ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := by
  first | exact @GlobalTheory.PoinTerm.norm_coef_le | exact GlobalTheory.PoinTerm.norm_coef_le | (intros; apply GlobalTheory.PoinTerm.norm_coef_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecayWeightOneParamTranslateLeConstMul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecayWeightOneParamTranslateLeConstMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.OnePDecay

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing

theorem hsn_eq_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : hsn A = ‖A‖ := by
  rw [hsn, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (Real.rpow_natCast _ 2).symm

theorem hsn_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : hsn (A * B) ≤ hsn A * hsn B := by
  rw [hsn_eq_norm, hsn_eq_norm, hsn_eq_norm]
  exact Matrix.frobenius_norm_mul A B

end Frob

theorem hsn_nonneg' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsn A := Real.sqrt_nonneg _

theorem continuous_hsn_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun s : ℝ => hsn (NormedSpace.exp (s • X) : Matrix (Fin n) (Fin n) ℂ) := by
  unfold hsn
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_)
  exact (continuous_iff_continuousAt.2 fun t => (GlobalTheory.Mem.Lift.hasDerivAt_exp_entry X t i j).continuousAt).norm.pow 2

theorem decay_oneP : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → ∀ N : ℕ, ∃ L : ℝ, 0 ≤ L ∧
      ∀ (x : GA D V) (t : ℝ), |t| < 1 → ∏ τ', ((1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N)⁻¹ ≤
        L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ N)⁻¹ := by
  intro D θ hθ V τ X hX N
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_hsn_exp X).continuousOn
  set m : ℝ := max 1 (max M (hsn (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))) with hmdef
  have hm1 : 1 ≤ m := le_max_left _ _
  have hbound : ∀ τ' (s : ℝ), |s| ≤ 1 → hsn (cmp θ τ' (oneP θ V τ X s)) ≤ m := by
    intro τ' s hs
    have h := GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX s
    by_cases e : τ' = τ
    · subst e
      show hsn (infMat _ _ (θ τ') _) ≤ m
      rw [h.2.1]
      have := hM s ⟨(abs_le.1 hs).1, (abs_le.1 hs).2⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_of_le_right (le_max_left _ _)))
    · show hsn (infMat _ _ (θ τ') _) ≤ m
      rw [h.2.2 τ' e]
      exact le_max_of_le_right (le_max_right _ _)
  have hkey : ∀ (x : GA D V) (t : ℝ) τ', |t| < 1 →
      1 + hsn (cmp θ τ' x) ≤ (1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) * m := by
    intro x t τ' ht
    have hx : x = x * oneP θ V τ X t * oneP θ V τ X (-t) := by
      rw [mul_assoc, ← GlobalTheory.Mem.Lift.oneP_add hθ hX, add_neg_cancel, GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one]
    have h1 : hsn (cmp θ τ' x) ≤ hsn (cmp θ τ' (x * oneP θ V τ X t)) * m := by
      have e2 : cmp θ τ' x = cmp θ τ' (x * oneP θ V τ X t) * cmp θ τ' (oneP θ V τ X (-t)) := by
        show infMat _ _ (θ τ') x = infMat _ _ (θ τ') _ * infMat _ _ (θ τ') _
        rw [← GlobalTheory.PointAtPlaceHom.infMat_mul, ← hx]
      rw [e2]
      exact (hsn_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (hbound τ' (-t) (by rw [abs_neg]; exact ht.le)) (hsn_nonneg' _))
    nlinarith [hsn_nonneg' (cmp θ τ' (x * oneP θ V τ X t))]
  refine ⟨m ^ (N * Fintype.card D.what₂.Tau), by positivity, fun x t ht => ?_⟩
  rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun τ' _ => inv_nonneg.2 (pow_nonneg (by linarith [hsn_nonneg' (cmp θ τ' (x * oneP θ V τ X t))]) N)) (fun τ' _ => ?_)
  have ha := hsn_nonneg' (cmp θ τ' (x * oneP θ V τ X t))
  have hb := hsn_nonneg' (cmp θ τ' x)
  have hk := hkey x t τ' ht
  have hpa : 0 < (1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N := pow_pos (by linarith) N
  have hpb : 0 < (1 + hsn (cmp θ τ' x)) ^ N := pow_pos (by linarith) N
  rw [← div_eq_mul_inv, le_div_iff₀ hpb, inv_mul_eq_div, ← div_pow]
  refine pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith)) ?_ N
  rw [div_le_iff₀ (by linarith)]
  linarith

end GlobalTheory.OnePDecay

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecayWeightOneParamTranslateLeConstMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decayWeight_oneParamTranslate_le_const_mul : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → ∀ N : ℕ, ∃ L : ℝ, 0 ≤ L ∧ ∀ (x : GA D V) (t : ℝ), |t| < 1 → ∏ τ', ((1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N)⁻¹ ≤ L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ N)⁻¹ := by
  first | exact @GlobalTheory.OnePDecay.decay_oneP | exact GlobalTheory.OnePDecay.decay_oneP | (intros; apply GlobalTheory.OnePDecay.decay_oneP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtLevelIndicatorCoefficientTestOneParam
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtLevelIndicatorCoefficientTestOneParam
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.TermDeriv

theorem hasDerivAt_coef_oneP : ∀ (D : D7), GlobalTheory.Published.HarishChandraModules → ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v b : ∀ τ, M.H τ) (τ : D.what₂.Tau), b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ → ∀ X ∈ lieAt V τ, ∀ x : GA D V, HasDerivAt (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) (coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x) 0 := by
  intro D hHC θ hθ V S M K v b τ hb X hX x
  have hfin : ∀ s : ℝ, Lev.finE V (x * oneP θ V τ X s) = Lev.finE V x := by
    intro s
    have h : finHom V (oneP θ V τ X s) = 1 := GlobalTheory.PointAtPlaceHom.atTau_mem V τ _
    show (Formalism.UG.bc (Lev.swapAE D)).comp (finHom V) (x * oneP θ V τ X s) = _
    rw [map_mul, MonoidHom.comp_apply (Formalism.UG.bc (Lev.swapAE D)) (finHom V) (oneP θ V τ X s), h, map_one, mul_one]
    rfl
  by_cases hK : Lev.finE V x ∈ K
  swap
  · have e : (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) = fun _ => 0 := by
      funext s
      simp only [coef, hfin s, hK, if_false]
    rw [e]
    have e2 : coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x = 0 := by
      simp only [coef, hK, if_false]
    rw [e2]
    exact hasDerivAt_const _ _
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hstd := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  have hsv : SmoothVec (lieAt V τ) (M.rep τ) (b τ) :=
    hHC.smoothVec hstd.1 hstd.2.1 hb (M.fr_unit τ) (M.fr_gram τ)
  have hd0 := Formalism.IndefR.SchurOrthogonalityAlt.gp_sv_hasDerivAt hsv hX 0
  rw [zero_smul, NormedSpace.exp_zero, Formalism.IndefR.SchurOrthogonalityAlt.gp_rep_one, ContinuousLinearMap.one_apply] at hd0
  set c : ℂ := ∏ τ' ∈ Finset.univ.erase τ, ⟪v τ', M.rep τ' (cmp θ τ' x) (b τ')⟫_ℂ with hc
  have hfun : ∀ s : ℝ, coef θ M K v b (x * oneP θ V τ X s) =
      c * ⟪v τ, M.rep τ (cmp θ τ x) (M.rep τ (NormedSpace.exp (s • X)) (b τ))⟫_ℂ := by
    intro s
    simp only [coef, hfin s, hK, if_true, coefR]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ)]
    congr 1
    · refine Finset.prod_congr rfl fun τ' hτ' => ?_
      have hne := Finset.ne_of_mem_erase hτ'
      have h := (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX s).2.2 τ' hne
      show ⟪v τ', M.rep τ' (infMat D.sp.cm.sig V.gram (θ τ') (x * oneP θ V τ X s)) (b τ')⟫_ℂ = _
      rw [GlobalTheory.PointAtPlaceHom.infMat_mul, h, Matrix.mul_one]
    · show ⟪v τ, M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) (x * oneP θ V τ X s)) (b τ)⟫_ℂ = _
      rw [GlobalTheory.PointAtPlaceHom.infMat_mul, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX s).2.1,
        Formalism.IndefR.SchurOrthogonalityAlt.rep_mul M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ) (GlobalTheory.Mem.Lift.exp_mem hX s)]
      rfl
  have hval : coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x =
      c * ⟪v τ, M.rep τ (cmp θ τ x) (dRep (M.rep τ) X (b τ))⟫_ℂ := by
    simp only [coef, hK, if_true, coefR]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun τ' hτ' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ')]
  rw [hval, show (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) = fun s : ℝ =>
      c * ⟪v τ, M.rep τ (cmp θ τ x) (M.rep τ (NormedSpace.exp (s • X)) (b τ))⟫_ℂ from funext hfun]
  refine HasDerivAt.const_mul c ?_
  exact (((innerSL ℂ (v τ)).comp (M.rep τ (cmp θ τ x))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd0

end GlobalTheory.TermDeriv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtLevelIndicatorCoefficientTestOneParamStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_levelIndicatorCoefficientTest_oneParam : ∀ (D : D7), GlobalTheory.Published.HarishChandraModules → ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v b : ∀ τ, M.H τ) (τ : D.what₂.Tau), b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ → ∀ X ∈ lieAt V τ, ∀ x : GA D V, HasDerivAt (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) (coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x) 0 := by
  first | exact @GlobalTheory.TermDeriv.hasDerivAt_coef_oneP | exact GlobalTheory.TermDeriv.hasDerivAt_coef_oneP | (intros; apply GlobalTheory.TermDeriv.hasDerivAt_coef_oneP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesSmoothModerateGrowthDeriv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.PoinDer

variable {D : D7}

theorem termBound (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ) (hv : KDecay M v) (b : ∀ τ, M.H τ)
    (hb : ∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : GA D V, ‖coef θ M K v b x‖ ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ :=
  GlobalTheory.T.norm_levelIndicatorCoefficientTest_le_decay D θ hθ V S M K v hv b hb

theorem sumBound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ →
    ∀ (𝔪 : Ideal (𝓞 D.host.E)) (c : GA D V), ∃ (C₀ : ℝ) (A : ℕ), ∀ (u : GA D V → ℝ) (C : ℝ), (∀ x, 0 ≤ u x) →
    (∀ x, Lev.finE V x ∉ congLev D.sp.cm V.gram Λ 𝔪 → u x = 0) →
    (∀ x, u x ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) → ∀ g : GA D V,
    Summable (fun γ : GQ V => u (c * (γ : GA D V) * g)) ∧ ∑' γ : GQ V, u (c * (γ : GA D V) * g) ≤ C * C₀ * height V g ^ A :=
  GlobalTheory.T.coefficientPoincareSeries_summable_majorant

theorem termDeriv (hHC : GlobalTheory.Published.HarishChandraModules) (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v b : ∀ τ, M.H τ)
    (τ : D.what₂.Tau) (hb : b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (x : GA D V) :
    HasDerivAt (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s))
      (coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x) 0 :=
  GlobalTheory.T.hasDerivAt_levelIndicatorCoefficientTest_oneParam D hHC θ hθ V S M K v b τ hb X hX x

theorem onePDecay (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (N : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (x : GA D V) (t : ℝ), |t| < 1 →
      ∏ τ', ((1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N)⁻¹ ≤ L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ N)⁻¹ :=
  GlobalTheory.T.decayWeight_oneParamTranslate_le_const_mul D θ hθ V τ X hX N

theorem finE_mul_oneP (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (x : GA D V) (t : ℝ) :
    Lev.finE V (x * oneP θ V τ X t) = Lev.finE V x := by
  have h : finHom V (oneP θ V τ X t) = 1 := GlobalTheory.PointAtPlaceHom.atTau_mem V τ _
  show (Formalism.UG.bc (Lev.swapAE D)).comp (finHom V) (x * oneP θ V τ X t) = (Formalism.UG.bc (Lev.swapAE D)).comp (finHom V) x
  rw [map_mul, MonoidHom.comp_apply (Formalism.UG.bc (Lev.swapAE D)) (finHom V) (oneP θ V τ X t), h, map_one, mul_one]

theorem poin_smooth_growth_deriv : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ UnifModGrowth V θ (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, (w : M.H τ) = dRep (M.rep τ) X (a τ) → (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ' => Function.update a τ w τ') = Rder θ V τ X (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  intro hHC D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c a
  obtain ⟨C₀, A, hB⟩ := sumBound D θ hθ V Λ hΛ 𝔪 c
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hK

  have hsum : ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∃ C : ℝ, ∀ g,
      Summable (fun γ : GQ V => ‖coef θ M K v b (c * (γ : GA D V) * g)‖) ∧
      ∑' γ : GQ V, ‖coef θ M K v b (c * (γ : GA D V) * g)‖ ≤ C * height V g ^ A := by
    intro b hb
    obtain ⟨C, hC0, hC⟩ := termBound θ hθ M K v hv b hb
    refine ⟨C * C₀, fun g => ?_⟩
    refine hB (fun x => ‖coef θ M K v b x‖) C (fun _ => norm_nonneg _) (fun x hx => ?_) hC g
    simp only [coef, if_neg hx, norm_zero]
  have grow : ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ModGrowthExp V A (poin θ M K v c b) := by
    intro b hb
    obtain ⟨C, hC⟩ := hsum b hb
    exact ⟨C, fun g => (norm_tsum_le_tsum_norm (hC g).1).trans (hC g).2⟩

  have der : ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∀ τ, ∀ X ∈ lieAt V τ, ∀ g,
      HasDerivAt (fun t : ℝ => poin θ M K v c b (g * oneP θ V τ X t))
        (poin θ M K v c (Function.update b τ (dRep (M.rep τ) X (b τ))) g) 0 := by
    intro b hb τ X hX g
    set b' := Function.update b τ (dRep (M.rep τ) X (b τ)) with hb'd
    have hb' : ∀ τ', b' τ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ' := by
      intro τ'
      by_cases h : τ' = τ
      · subst h
        rw [hb'd, Function.update_self]
        exact GlobalTheory.GKUnif.dRep_mem_kFin hHC M τ' hX (hb τ')
      · rw [hb'd, Function.update_of_ne h]
        exact hb τ'
    obtain ⟨C', hC'0, hC'⟩ := termBound θ hθ M K v hv b' hb'
    obtain ⟨L, hL0, hL⟩ := onePDecay θ hθ V τ hX (2 * V.rank ^ 2 + 1)
    set u : GA D V → ℝ := fun x => if Lev.finE V x ∈ K then C' * L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ else 0
      with hu
    have hprod : ∀ x : GA D V, 0 ≤ ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := fun x =>
      Finset.prod_nonneg fun τ' _ => inv_nonneg.2 (pow_nonneg (by unfold hsn; positivity) _)
    have hu0 : ∀ x, 0 ≤ u x := fun x => by
      simp only [hu]; split_ifs
      · exact mul_nonneg (mul_nonneg hC'0 hL0) (hprod x)
      · exact le_rfl
    have huK : ∀ x, Lev.finE V x ∉ K → u x = 0 := fun x hx => by simp only [hu, if_neg hx]
    have huC : ∀ x, u x ≤ (C' * L) * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := fun x => by
      simp only [hu]; split_ifs
      · exact le_rfl
      · exact mul_nonneg (mul_nonneg hC'0 hL0) (hprod x)
    have hbd : ∀ (x : GA D V) (y : ℝ), y ∈ Set.Ioo (-1 : ℝ) 1 → ‖coef θ M K v b' (x * oneP θ V τ X y)‖ ≤ u x := by
      intro x y hy
      by_cases hx : Lev.finE V x ∈ K
      · have h1 := hC' (x * oneP θ V τ X y)
        have h2 := hL x y (abs_lt.2 ⟨hy.1, hy.2⟩)
        simp only [hu, if_pos hx]
        calc _ ≤ _ := h1
          _ ≤ C' * (L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) := mul_le_mul_of_nonneg_left h2 hC'0
          _ = _ := by ring
      · have : coef θ M K v b' (x * oneP θ V τ X y) = 0 := by
          simp only [coef, finE_mul_oneP, if_neg hx]
        rw [this, norm_zero]
        exact hu0 x
    have hS := (hB u (C' * L) hu0 huK huC g).1
    obtain ⟨Cb, hCb⟩ := hsum b hb
    have key := hasDerivAt_tsum_of_isPreconnected (g := fun (γ : GQ V) (s : ℝ) => coef θ M K v b (c * (γ : GA D V) * g * oneP θ V τ X s))
      (g' := fun (γ : GQ V) (s : ℝ) => coef θ M K v b' (c * (γ : GA D V) * g * oneP θ V τ X s)) (t := Set.Ioo (-1 : ℝ) 1)
      (y₀ := 0) (y := 0) hS isOpen_Ioo isPreconnected_Ioo
      (fun γ y _ => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun x => termDeriv hHC θ hθ M K v b τ (hb τ) hX x) _ y)
      (fun γ y hy => hbd _ y hy) (by norm_num)
      (by simpa [GlobalTheory.Mem.Lift.oneP_zero hθ] using (hCb g).1.of_norm) (by norm_num)
    simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at key
    refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [poin, mul_assoc]
  refine ⟨?_, ⟨A, fun l hl => ?_⟩, ?_⟩
  ·
    refine GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ V
      {φ | ∃ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) ∧ φ = poin θ M K v c b} ?_ ?_ _ ⟨_, fun τ => (a τ).2, rfl⟩
    · rintro φ ⟨b, hb, rfl⟩
      exact (((GlobalTheory.T.coefficientPoincareSeries_isAutomorphic D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c).1 fun τ => ⟨b τ, hb τ⟩).1).cont
    · rintro φ ⟨b, hb, rfl⟩ τ X hX
      refine ⟨_, ⟨Function.update b τ (dRep (M.rep τ) X (b τ)), fun τ' => ?_, rfl⟩, der b hb τ X hX⟩
      by_cases h : τ' = τ
      · subst h
        rw [Function.update_self]
        exact GlobalTheory.GKUnif.dRep_mem_kFin hHC M τ' hX (hb τ')
      · rw [Function.update_of_ne h]
        exact hb τ'
  ·
    have claim : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
        ∃ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) ∧
          l.foldr (fun p f => Rder θ V p.1 p.2 f) (poin θ M K v c fun τ => a τ) = poin θ M K v c b := by
      intro l
      induction l with
      | nil => exact fun _ => ⟨fun τ => a τ, fun τ => (a τ).2, rfl⟩
      | cons p l ih =>
        intro hl'
        obtain ⟨b, hb, e⟩ := ih fun q hq => hl' q (List.mem_cons_of_mem _ hq)
        have hX : p.2 ∈ lieAt V p.1 := hl' p List.mem_cons_self
        refine ⟨Function.update b p.1 (dRep (M.rep p.1) p.2 (b p.1)), fun τ' => ?_, ?_⟩
        · by_cases h : τ' = p.1
          · rw [h, Function.update_self]
            exact GlobalTheory.GKUnif.dRep_mem_kFin hHC M p.1 hX (hb p.1)
          · rw [Function.update_of_ne h]
            exact hb τ'
        · rw [List.foldr_cons, e]
          funext g
          exact (der b hb p.1 p.2 hX g).deriv
    obtain ⟨b, hb, e⟩ := claim l hl
    rw [e]
    exact grow b hb
  ·
    intro τ X hX w hw
    funext g
    have e : (fun τ' => (Function.update a τ w τ' : M.H τ')) =
        Function.update (fun τ' => (a τ' : M.H τ')) τ (dRep (M.rep τ) X (a τ)) := by
      funext τ'
      by_cases h : τ' = τ
      · subst h
        simp [hw]
      · simp [Function.update_of_ne h]
    rw [e]
    exact ((der (fun τ' => a τ') (fun τ' => (a τ').2) τ X hX g).deriv).symm

end GlobalTheory.PoinDer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesSmoothModerateGrowthDerivStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareSeries_smooth_moderateGrowth_deriv : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ UnifModGrowth V θ (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, (w : M.H τ) = dRep (M.rep τ) X (a τ) → (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ' => Function.update a τ w τ') = Rder θ V τ X (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  first | exact @GlobalTheory.PoinDer.poin_smooth_growth_deriv | exact GlobalTheory.PoinDer.poin_smooth_growth_deriv | (intros; apply GlobalTheory.PoinDer.poin_smooth_growth_deriv <;> assumption)
end
