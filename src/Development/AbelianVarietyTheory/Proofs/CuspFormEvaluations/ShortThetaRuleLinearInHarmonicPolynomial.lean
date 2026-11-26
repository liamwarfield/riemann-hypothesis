module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeExpOfLogLe
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaValueStandardLatticeEqClassicalTheta
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetTranslateProjectedVacuumLe
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIntegralHarmonicNeZeroAndIsHomogeneous
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevelTranslateJetNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaRuleLinearInHarmonicPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaRuleLinearInHarmonicPolynomial
noncomputable section

namespace GlobalTheory.ShortRuleLinear

section General

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem map_mem_HHa {F F₂ : IntermediateField ℚ ℂ} (h : F = F₂) {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) F}
    (hP : P ∈ HHa Dw.mult n F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) :
    MvPolynomial.map (IntermediateField.equivOfEq h : F →+* F₂) P ∈
      HHa Dw.mult n F₂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
  subst h
  have e : (IntermediateField.equivOfEq (rfl : F = F) : F →+* F) = RingHom.id F := RingHom.ext fun _ => rfl
  rw [e, MvPolynomial.map_id]
  exact hP

theorem eq_sum_of_isShortRule (hC : ChartIndepSt2) (Xo : Moduli Dw l) (c : Coeff l) {n : ℕ} (d : DeltaDat Xo c n)
    (hd : d.IsLev) [StarRing (𝓞 E)] (hn : IsNab d.Xo₂ d.c₂ d.nab₂) (a : (E →+* ℂ) × ℕ → ℕ) (Λ : GenLat E n) (N : ℕ)
    (x0 : Fin n → Dw.La) (hU : Λ.Unimod) (hT : Λ.TrivAt d.l₂.M) (hL : Λ.LevOK N d.l₂.M) (m : ℕ) (cf : Fin m → c.F)
    (Q : Fin m → MvPolynomial (LtN Dw n) c.F) (g : Rul Xo c) (gs : Fin m → Rul Xo c)
    (hQ : ∀ i, Q i ∈ harmL c Λ a) (hg : g ∈ sec Xo c a n) (hgs : ∀ i, gs i ∈ sec Xo c a n)
    (hr : IsShortRule Xo c d Λ N x0 (∑ i, cf i • Q i) g) (hrs : ∀ i, IsShortRule Xo c d Λ N x0 (Q i) (gs i)) :
    g = ∑ i, cf i • gs i := by
  rw [← sub_eq_zero]
  refine GlobalTheory.Frames.ptsDetect_framed E H Dw l Xo c a n _
    (Submodule.sub_mem _ hg (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hgs i))) ?_
  intro k _ _ _ y
  let _ : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have hk : ∀ x : c.F, algebraMap d.c₂.F k (d.eF x) = algebraMap c.F k x := fun x => by
    show algebraMap c.F k (d.eF.symm (d.eF x)) = _
    rw [AlgEquiv.symm_apply_apply]
  obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
  obtain ⟨v, hv, e⟩ := hr k hk y y₂ hy
  choose u hu eu using fun i => hrs i k hk y y₂ hy
  have hm : MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (∑ i, cf i • Q i) =
      ∑ i, d.eF (cf i) • MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (Q i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
    rfl
  rw [hm] at hv
  have hlin := GlobalTheory.T.short_theta_value_linear_in_polynomial hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hn n Λ N hU hT hL a (d.w x0) _ m (fun i => d.eF (cf i))
    (fun i => MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (Q i)) (fun i => map_mem_HHa d.hF.symm (hQ i).1) k y₂ v u hv hu
  let L := evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
  have hL : ∀ f, L f = evR Xo c f y := fun _ => rfl
  change L (g - ∑ i, cf i • gs i) = 0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, hL, e, hlin, Finset.mul_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hL, eu, hk, Algebra.smul_def]
  ring

end General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem shortRule_linear : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), LawsSh T → ∀ (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La), Λ.Unimod → Λ.TrivAt (T.dδ j w.n).l₂.M → Λ.LevOK N (T.dδ j w.n).l₂.M → ∀ (m : ℕ) (cf : Fin m → T.Q.c.F) (Q : Fin m → MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (g : T.R j) (gs : Fin m → T.R j), (∀ i, Q i ∈ harmL T.Q.c Λ (wtA w)) → g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → (∀ i, gs i ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n) → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 (∑ i, cf i • Q i) g → (∀ i, IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 (Q i) (gs i)) → g = ∑ i, cf i • gs i := by
  intro hC D T _ hS j hj w Λ N x0 hU hT hL m cf Q g gs hQ hg hgs hr hrs
  obtain ⟨_, hn⟩ := hS.dNab j hj w.n
  exact eq_sum_of_isShortRule hC (T.Q.Xo j) T.Q.c (T.dδ j w.n) (hS.dLev j hj w.n) hn (wtA w) Λ N x0 hU hT hL m cf Q g gs
    hQ hg hgs hr hrs

end GlobalTheory.ShortRuleLinear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaRuleLinearInHarmonicPolynomialStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortThetaRule_linear_in_harmonic_polynomial : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), LawsSh T → ∀ (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La), Λ.Unimod → Λ.TrivAt (T.dδ j w.n).l₂.M → Λ.LevOK N (T.dδ j w.n).l₂.M → ∀ (m : ℕ) (cf : Fin m → T.Q.c.F) (Q : Fin m → MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (g : T.R j) (gs : Fin m → T.R j), (∀ i, Q i ∈ harmL T.Q.c Λ (wtA w)) → g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → (∀ i, gs i ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n) → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 (∑ i, cf i • Q i) g → (∀ i, IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 (Q i) (gs i)) → g = ∑ i, cf i • gs i := by
  first | exact @GlobalTheory.ShortRuleLinear.shortRule_linear | exact GlobalTheory.ShortRuleLinear.shortRule_linear | (intros; apply GlobalTheory.ShortRuleLinear.shortRule_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGeneratorPointwiseBoundOrthonormalFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGeneratorPointwiseBoundOrthonormalFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ThetaPt

theorem isUnitFr_of_isOrtho {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
    {x : Frame X.Ψ r} (ho : X.IsOrtho x) : IsUnitFr X x := by
  intro τ i

  simp only [dmin, lminor]
  rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp_apply, sgn]
  split_ifs <;> simp

theorem sum_norm_coeff_rename_map {K α β : Type} [Field K] (σ : K →+* ℂ) (e : α ≃ β) (P : MvPolynomial α K) :
    ∑ m ∈ (MvPolynomial.rename e (MvPolynomial.map σ P)).support,
      ‖(MvPolynomial.rename e (MvPolynomial.map σ P)).coeff m‖ = ∑ m ∈ P.support, ‖σ (P.coeff m)‖ := by
  classical
  rw [MvPolynomial.support_rename_of_injective e.injective,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective e.injective h]
  simp only [MvPolynomial.coeff_rename_mapDomain _ e.injective, MvPolynomial.coeff_map]
  rw [MvPolynomial.support_map_of_injective _ σ.injective]

theorem theta_bound_ortho : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab → ∀ (xx : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab xx P f → ∀ k (x : (U.X k).dom), (U.X k).IsOrtho x.1 → ∀ lam : ℝ, 0 < lam → lam ^ 2 ≤ (U.X k).firstMinimumSq x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ≤ (∑ m ∈ P.support, ‖σ (P.coeff m)‖) * (Real.pi * Real.exp 1 * t * (Formalism.L2.Pj.DF Dw a : ℕ)) ^ (((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (fdeg E * r : ℕ) * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (fdeg E * r * n) := by
  intro hCI E _ _ _ H Dw l Xo c σ r U hG hU hr1 t ht hc a n hDom _ nab hnab xx P hP f hf k x ho lam hlam hla

  have hunit : IsUnitFr (U.X k) x.1 := isUnitFr_of_isOrtho ho
  obtain ⟨W, Dc, A, θ, v, κ, hDe, hWg, hw0, hSD, hmark, hAm, hRead, hth1, hmean, hvac, hprod⟩ :=
    GlobalTheory.Dict.VSetup.exists_setup E H Dw l Xo c σ r U hG hU hr1 a n hDom k x hunit
  let _ : Algebra c.F ℂ := σ.toAlgebra
  have hn : Even n := hDom.2

  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨Yr, hYr⟩ : ∃ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E,
      IsRoots l (U.X k).Λ (W.mark k) l.M Y := by
    exact (DualMark.dual_marking E H Dw l r (U.X k) (U.X k).Λ (W.mark k) _ hSD hmark
      (Complex.isPrimitiveRoot_exp l.M hM.ne')).2.2.2.2 n l.M hM
  set Y := Yr fun b => (Submodule.Quotient.mk (xx b) : LevQ Dw l)
  have hY : ∀ b, (∃ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), a - xx b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ∧
        Y b - ((l.M : E)⁻¹) • W.mark k a ∈ (U.X k).Λ) ∧
        ∃ j : ℕ, ∀ s ∈ l.Mb ^ j, ∃ u ∈ (U.X k).Λ, s • Y b = (2 * l.M) • u := by
    intro b
    obtain ⟨⟨a', ha', hq, hmem⟩, hj⟩ := hYr (fun b => (Submodule.Quotient.mk (xx b) : LevQ Dw l)) b
    exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1 hq, hmem⟩, hj⟩

  have hval := (GlobalTheory.thetaRule_exists_and_eval hCI E H Dw l Xo c nab hnab a n xx P hP).2 f hf ℂ (unC U k x)
  have hdir : ∀ ℓ, letterDir (U.X k) Dc.hr Dc.idx (Dc.eL ℓ) =
      Pi.single ℓ.2.2 (Pi.single (W.e.symm ⟨ℓ.1, ℓ.2.1⟩) 1) := hDe ▸ Dc.dir_eq
  have heq := GlobalTheory.Dict.thVal_eq_thP hCI E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ
    (unC U k x) A Dc.sympl x.2 hSD Dw.p n Dc.hr Dc.eL hU.1 hn hdir nab hnab θ v κ hRead hvac hprod
    (W.mark k) hmark hAm xx Y hY a P hP _ hval

  have hstd : stdL E n ∈ Vset E n 1 := Base.stdL_mem_Vset n 1
  have hint : IsIntegral ℤ ((H.w0 : 𝓞 E) : E) := (H.w0).isIntegral_coe
  have hproj : projA (U.X k) Dc.bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v = v := by
    rw [(GlobalTheory.SW.TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn (H.w0 : E) hint hw0 (U.X k).Λ hSD 1
      (stdL E n) hstd).2.2.1 v hvac.1 v hvac, hvac.2.1, one_smul]

  have hlamL : ∀ u ∈ (U.X k).Λ, u ≠ 0 →
      lam ^ 2 ≤ (hx (U.X k) Dc.bas Dc.idx x.1 (pv (U.X k) Dc.idx x.1 u) (pv (U.X k) Dc.idx x.1 u)).re :=
    fun u hu hne => hla.trans ((GlobalTheory.Dict.hx_ortho E r (U.X k) W.g Dc.bas Dc.idx Dc.sympl x.1 x.2 ho).2.2.1 u hu hne)

  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).IsHomogeneous (DF Dw a) :=
    (((GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous E H Dw l c a n).2 P
      (by unfold harmA at hP; unfold HaO at hP; exact hP.1)).map _).rename_isHomogeneous
  have hb := GlobalTheory.Dict.VacJet.jet_projA_le E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn H.w0 hw0
    (U.X k).Λ hSD (stdL E n) hstd v hvac x.1 x.2 ho t ht (hc k) θ κ hth1 hmean hprod lam hlam hlamL Y
    (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)) (DF Dw a) hhom

  rw [hproj, AddSubgroup.relIndex_self, Nat.cast_one, one_pow, Real.sqrt_one, _root_.mul_one] at hb
  have hsum : ∑ m ∈ (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).support,
      ‖(MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).coeff m‖ =
        ∑ m ∈ P.support, ‖σ (P.coeff m)‖ := sum_norm_coeff_rename_map σ Dc.eL P
  have hgR : ((W.g : ℕ) : ℝ) = ((fdeg E * r : ℕ) : ℝ) := by rw [hWg]
  have hgn : W.g * n = fdeg E * r * n := by rw [hWg]
  rw [hsum, hgR, hgn] at hb
  have hv0 : Formalism.L2.PjFree.toC (evR Xo c f (U.un k x)) = evR Xo c f (unC U k x) := rfl
  rw [hv0, heq]
  exact hb

end GlobalTheory.Dict.ThetaPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGeneratorPointwiseBoundOrthonormalFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGenerator_pointwise_bound_orthonormal_frame : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab → ∀ (xx : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab xx P f → ∀ k (x : (U.X k).dom), (U.X k).IsOrtho x.1 → ∀ lam : ℝ, 0 < lam → lam ^ 2 ≤ (U.X k).firstMinimumSq x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ≤ (∑ m ∈ P.support, ‖σ (P.coeff m)‖) * (Real.pi * Real.exp 1 * t * (Formalism.L2.Pj.DF Dw a : ℕ)) ^ (((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (fdeg E * r : ℕ) * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (fdeg E * r * n) := by
  first | exact @GlobalTheory.Dict.ThetaPt.theta_bound_ortho | exact GlobalTheory.Dict.ThetaPt.theta_bound_ortho | (intros; apply GlobalTheory.Dict.ThetaPt.theta_bound_ortho <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGeneratorReadingNeZeroAtFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGeneratorReadingNeZeroAtFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.ThetaNoZero

theorem mem_mul_smul_top {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {I J : Ideal R}
    (h : I ⊔ J = ⊤) {x : M} (hI : x ∈ I • (⊤ : Submodule R M)) (hJ : x ∈ J • (⊤ : Submodule R M)) :
    x ∈ (I * J) • (⊤ : Submodule R M) := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top : (1 : R) ∈ I ⊔ J)
  have e : x = i • x + j • x := by rw [← add_smul, hij, one_smul]
  rw [e]
  refine Submodule.add_mem _ ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul hi hJ
  · rw [mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hj hI

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem dmin_of_isOrtho {X : Data E r} {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
  unfold dmin lminor psgn
  rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, Complex.ofReal_prod,
    ← Fin.prod_univ_eq_prod_range fun a => ((FD.sgn X.p0 a : ℝ) : ℂ)]
  rfl

theorem psgn_mul_self (p i : ℕ) : psgn p i * psgn p i = 1 := by
  unfold psgn
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold FD.sgn
  split_ifs <;> simp

theorem isUnitFr_of_isOrtho {X : Data E r} {x : Frame X.Ψ r} (ho : X.IsOrtho x) : IsUnitFr X x := by
  intro τ i
  rw [dmin_of_isOrtho ho, Complex.norm_real, Real.norm_eq_abs]
  have h := psgn_mul_self X.p0 i
  rcases mul_self_eq_one_iff.1 h with h | h <;> simp [h]

theorem rmul_mem_dom_of_isOrtho {X : Data E r} {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r)
    (ho : X.IsOrtho (rmul x b)) : rmul x b ∈ X.dom := by
  refine fun τ => ⟨?_, fun i => ?_⟩
  · change (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 (hb τ).1
  · rw [dmin_of_isOrtho ho, Complex.ofReal_re, psgn_mul_self]
    exact one_pos

theorem mark_sub_mem {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {L : Lt E r}
    {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hm : IsMark l L mk) {a a' : Dw.La}
    (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) (ha' : a' ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La))
    (h : a' - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ((l.M : E)⁻¹) • mk a' - ((l.M : E)⁻¹) • mk a ∈ L := by
  have h1 := mem_mul_smul_top l.coprime h (Submodule.sub_mem _ ha' ha)
  rw [l.prod, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨z, -, hz⟩ := h1
  have hM : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  rw [← smul_sub, ← map_sub, ← hz, map_smul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul,
    inv_mul_cancel₀ hM, one_smul]
  exact hm.mem z

theorem exists_thGen_rdU_ne_zero : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → r ≤ n → 3 * Formalism.L2.Pj.DF Dw a + 2 ≤ l.M → ∀ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab → ∀ k, ∀ x ∈ (U.X k).dom, ∃ f ∈ thGen Xo c nab a n, Formalism.L2.PjFree.rdU U f k x ≠ 0 := by
  intro hCI E _ _ _ H Dw l Xo c σ r U hσ hU hr t ht hc a n hdom hrn hM _ nab hnab k x hx
  have hrpq : r = Dw.p + Dw.q := hU.1
  obtain ⟨x₀, b, hb, ho, rfl⟩ := (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r (U.X k).p0 (U.X k).Ψ
    (U.X k).Gm (U.X k).Gm_herm).1 x hx
  have ho : (U.X k).IsOrtho (rmul x b) := ho
  have hx₀ := rmul_mem_dom_of_isOrtho hx hb ho
  obtain ⟨⟨P, hP, hP0⟩, hhom⟩ : (∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0) ∧ _ :=
    ⟨(GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous E H Dw l c a n).1 hdom (hrpq ▸ hrn),
      (GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous E H Dw l c a n).2⟩
  have hdeg : P.totalDegree ≤ Formalism.L2.Pj.DF Dw a := (hhom P hP.1).totalDegree_le
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨W, Dc, A, θ, v, κ, he, -, hw, hsd, hmk, hmarked, hreads, hth, hmean, hvac, hprod⟩ :=
    GlobalTheory.T.exists_analyticData_unitFrame_framedPoint E H Dw l Xo c σ r U hσ hU hr a n hdom k ⟨rmul x b, hx₀⟩ (isUnitFr_of_isOrtho ho)
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hME : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 hM0
  obtain ⟨-, -, hconj, hmul, hroots⟩ := GlobalTheory.T.dual_half_level_marking_exists_and_match E H Dw l r (U.X k) (U.X k).Λ (W.mark k) _ hsd hmk
    (Complex.isPrimitiveRoot_exp l.M hM0)
  obtain ⟨Y, hY⟩ := hroots n l.M (Nat.pos_of_ne_zero hM0)
  have hQ0 : MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P) ≠ 0 := by
    intro h0
    refine hP0 (MvPolynomial.map_injective (algebraMap c.F ℂ) (algebraMap c.F ℂ).injective
      (MvPolynomial.rename_injective _ Dc.eL.injective ?_))
    rw [h0, map_zero, map_zero]
  have hQd : (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).totalDegree ≤
      Formalism.L2.Pj.DF Dw a :=
    (((hhom P hP.1).map (algebraMap c.F ℂ)).rename_isHomogeneous (f := Dc.eL)).totalDegree_le
  obtain ⟨y, hy, hne⟩ := GlobalTheory.T.exists_level_translate_jet_ne_zero_alt E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hdom.2 H.w0 hw
    (U.X k).Λ hsd (rmul x b) hx₀ ho t ht (hc k) (Mfr l) l.M l.odd (by rw [hconj, hmul]) v hvac θ κ hth hmean hprod
    _ hQ0 (by omega)
  choose xs hxs u hu hyx using fun j => hmk.surj _ (hy j)
  obtain ⟨⟨f, hf, hfs⟩, hev⟩ := GlobalTheory.thetaRule_exists_and_eval hCI E H Dw l Xo c nab hnab a n xs P hP
  have hval := GlobalTheory.T.thetaValue_standardLattice_eq_classicalTheta hCI E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e (rmul x b) (U.X k).Λ
    (unC U k ⟨rmul x b, hx₀⟩) A Dc.sympl hx₀ hsd Dw.p n Dc.hr Dc.eL hrpq hdom.2 (he ▸ Dc.dir_eq) nab hnab θ v κ
    hreads hvac hprod (W.mark k) hmk hmarked xs (Y fun j => Submodule.Quotient.mk (xs j))
    (fun j => by
      obtain ⟨⟨a', ha', hq, hYa⟩, hj⟩ := hY (fun j => Submodule.Quotient.mk (xs j)) j
      exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1 hq, hYa⟩, hj⟩)
    a P hP _ (hev f hf ℂ (unC U k ⟨rmul x b, hx₀⟩))
  have hne' := hne (Y fun j => Submodule.Quotient.mk (xs j)) fun j => by
    obtain ⟨⟨a', ha', hq, hYa⟩, -⟩ := hY (fun j => Submodule.Quotient.mk (xs j)) j
    have h1 := mark_sub_mem hmk (hxs j) ha' ((Submodule.Quotient.eq _).1 hq)
    have h2 : y j = ((l.M : E)⁻¹) • W.mark k (xs j) + u j := by
      have := congrArg (fun z => ((l.M : E)⁻¹) • z) (hyx j)
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hME, one_smul, ← Nat.cast_smul_eq_nsmul E l.M (u j)] at this
      exact this
    have h3 := Submodule.sub_mem _ (Submodule.add_mem _ hYa h1) (hu j)
    convert h3 using 1
    rw [h2]
    abel
  rw [← hval] at hne'
  refine ⟨f, ⟨xs, P, hP, hf⟩, fun h0 => hne' ?_⟩
  have hB := (hU.2.2.2.2.1 a n hdom f hfs k).2.1 x hx b hb
  rw [h0, mul_zero] at hB
  have e : Formalism.L2.PjFree.rdU U f k (rmul x b) = Formalism.L2.PjFree.toC (evR Xo c f (U.un k ⟨rmul x b, hx₀⟩)) := dif_pos hx₀
  exact e.symm.trans hB

end GlobalTheory.ThetaNoZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGeneratorReadingNeZeroAtFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaGenerator_reading_ne_zero_at_frame : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → r ≤ n → 3 * Formalism.L2.Pj.DF Dw a + 2 ≤ l.M → ∀ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab → ∀ k, ∀ x ∈ (U.X k).dom, ∃ f ∈ thGen Xo c nab a n, Formalism.L2.PjFree.rdU U f k x ≠ 0 := by
  first | exact @GlobalTheory.ThetaNoZero.exists_thGen_rdU_ne_zero | exact GlobalTheory.ThetaNoZero.exists_thGen_rdU_ne_zero | (intros; apply GlobalTheory.ThetaNoZero.exists_thGen_rdU_ne_zero <;> assumption)
end
end
